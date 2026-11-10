-- Prove2me | Theorems.Thm_QThermalClassical_lemma_9
-- name    : QThermalClassical.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:09.092075+00:00
-- url     : https://prove2.me/theorems/5f1b1c39-04ba-42b6-8d21-68825e47db36
-- title:
--   Lemma 9 — propagator sampling $\mathbb E[I+bE]$ with $|b|\le(6\beta ks)^t$
-- statement:
--   Under the assumptions of Lemma 8 (an $(s,k)$-long-range Pauli Hamiltonian, $s,k>0$, a set $K$ of at most $k$ qubits met by some term of $H$), and for $\beta\ge0$, there is a distribution over tuples $(b,E)$ such that
--   $$
--   e^{-\beta H}e^{\beta(H-H_{(K)})}=\sum_{t=0}^\infty\frac{\beta^t}{t!}f_t(H,H_{(K)})=\mathbb E\left[I+bE\right],
--   $$
--   where:
--   1. $E$ is a Pauli product (up to a phase $\omega\in\{\pm1,\pm i\}$) of an ordered list $C(E)$ of terms of $H$;
--   2. the order $t=|C(E)|$ satisfies $t\ge1$;
--   3. $|b|\le(6\beta ks)^t$.
--
--   The distribution is organized by order: block $t$ has probability $2^{-t}$ and collects the outcomes of order $t$, and the expectation sums the blocks as a series. This primitive feeds the pinning procedure of Lemma 14.
--
--   Differences from the source:
--   - generalization: a label $a^*\in A$ → a site set $K$ with $|K|\le k$ met by some term of $H$; reason: the proof uses only $|\mathrm{supp}(P_{a^*})|\le k$; a non-identity label meets its own support; the proof of Theorem 1(a) needs partially pinned labels (p.26)
--   - reading: a distribution over $(b,E)$ and $\mathbb E_i[I+b_iE_i]$ → a sampler whose block $t$ holds the outcomes of order $t$, the expectation being the series over blocks of finite conditional means; reason: the grouping of (75); under it (73) holds for every $\beta\ge0$, without the condition $\beta<1/(6ks)$ the proof uses for summing over all outcomes at once
--   - reading: $E_i$ decomposes as a product of $a\in C(E_i)$, a Pauli product up to a phase → $E=\omega\cdot$(product of a reordering of $C(E)$), $\omega\in\{\pm1,\pm i\}$; reason: the proof: $Y/\|Y\|$ is a Pauli product up to a phase; $C(E)$ is chosen existentially, so the reordering changes nothing
--   - reading: $\beta$ unrestricted in the statement → $\beta\ge0$; reason: $\beta$ is an inverse temperature (eqs. (9), (22)); for $\beta<0$ and odd $t$ the printed bound $(6\beta ks)^t$ is negative
--   - reading: the sentence "If $\beta\le1/(6ks)$ then the coefficients $b_i$ are exponentially suppressed in $t_i$" → no separate clause; reason: it is a comment on the bound $|b|\le(6\beta ks)^t$
--   - encoding: a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ with distinct non-identity Pauli strings → a coefficient function $c$ on Pauli words with $c(I)=0$, $A=\{P: c_P\neq 0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 9, eq. (73), p.24, with eq. (75)

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_restrictTouching
import Definitions.Def_QThermalClassical_propagator
import Definitions.Def_QThermalClassical_IsPauliProd
import Definitions.Def_QThermalClassical_Sampler

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 9 (Propagator sampling).** Under the assumptions of Lemma 8 (with a site set `K`,
`|K| ≤ k`, met by some term of `H`), and `β ≥ 0`, there is a distribution over tuples
`(b, E)` with `e^{−βH} e^{β(H − H_{(K)})} = Σ_t (β^t/t!) f_t = 𝔼[I + bE]`, where `|b| ≤ (6βks)^t`,
`E` is a Pauli product (up to a phase) of an ordered list `C(E)` of terms of `H`, and
`t = |C(E)| ≥ 1` is the order of `E`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 9, eq. (73), p.24, with eq. (75).

**Formalization Note.** The distribution is a `Sampler` whose block `t` consists of the
outcomes of order `t` (the grouping of (75)), and the expectation is taken block by block
(`Sampler.HasExpect`). The label `a*` enters only through its site set `K`; the hypothesis
that some term meets `K` holds for `K = supp(P_{a*})` with `a* ∈ A`. The last sentence of the
lemma ("if `β ≤ 1/(6ks)` then the coefficients are exponentially suppressed") is a comment on
the bound and is not a separate clause. -/
theorem lemma_9 {Q : Type} [Fintype Q] [DecidableEq Q] (s k : ℝ) (hs : 0 < s) (hk : 0 < k)
    (c : PauliWord Q → ℝ) (hc : IsLongRangePauli s k c) (K : Finset Q)
    (hK : (K.card : ℝ) ≤ k) (hmeet : ∃ P, c P ≠ 0 ∧ (pauliSupport P ∩ K).Nonempty)
    (β : ℝ) (hβ : 0 ≤ β) :
    HasSum (fun t : ℕ => (β ^ t / (t.factorial : ℝ)) • fSeq (ham c) (ham (touching c K)) t)
      (propagator (ham c) (ham (touching c K)) β) ∧
    ∃ σ : Sampler Q,
      (∀ t j, (σ.o t j).C.length = t ∧ 1 ≤ (σ.o t j).C.length ∧
        (∀ a ∈ (σ.o t j).C, c a ≠ 0) ∧ IsPauliProd (σ.o t j).C (σ.o t j).E ∧
        |(σ.o t j).b| ≤ (β * 6 * k * s) ^ (σ.o t j).C.length) ∧
      σ.HasExpect (fun o => 1 + ((o.b : ℝ) : ℂ) • o.E)
        (propagator (ham c) (ham (touching c K)) β) := by sorry

end QThermalClassical
