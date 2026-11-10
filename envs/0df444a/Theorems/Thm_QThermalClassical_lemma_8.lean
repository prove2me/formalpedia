-- Prove2me | Theorems.Thm_QThermalClassical_lemma_8
-- name    : QThermalClassical.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:52.354119+00:00
-- url     : https://prove2.me/theorems/45036592-0b05-4c5e-9a0e-a7db3f79a321
-- title:
--   Lemma 8 — propagator expansion with on-site bound $\prod_{i=1}^t(ks+2ksi)\le(3ks)^tt!$
-- statement:
--   Let $H=\sum_a\lambda_aP_a$ be an $(s,k)$-long-range Pauli Hamiltonian with $s,k>0$, and let $K$ be a set of at most $k$ qubits (for instance $K=\mathrm{supp}(P_{a^*})$ for a label $a^*\in A$). Then for every real $\beta$
--   $$
--   e^{-\beta H}e^{\beta(H-H_{(K)})}=\sum_{t=0}^\infty\frac{\beta^t}{t!}f_t(H,H_{(K)}),
--   $$
--   where $f_0=I$ and $f_{t+1}=-[H,f_t]-f_tH_{(K)}$. Moreover, for every $t\ge1$, $f_t$ is a real combination
--   $$
--   f_t(H,H_{(K)})=\sum_j\mu_j\,P_{\vec b_j}
--   $$
--   of products $P_{\vec b_j}$ of the terms of connected sequences $\vec b_j\in Q^{(t)}_K$ (each product taken in some order of its factors), with $|\mathrm{supp}(P_{\vec b_j})|\le kt$ and
--   $$
--   \sum_j|\mu_j|\le\prod_{i=1}^t(ks+2ksi)\le\prod_{i=1}^t(3ksi)=(3ks)^tt!\qquad(56).
--   $$
--
--   The on-site bound replaces the degree bound of earlier expansions; this is the convergence input for the sampling primitive of Lemma 9.
--
--   Differences from the source:
--   - generalization: a label $a^*\in A$, $H_{(a^*)}$, $Q^{(t)}_{a^*}$ → any site set $K$ with $|K|\le k$, $H_{(K)}$, $Q^{(t)}_K$; reason: the proof uses only $|\mathrm{supp}(P_{a^*})|\le k$; $K=\mathrm{supp}(P_{a^*})$ gives the printed lemma, and the proof of Theorem 1(a) applies it to partially pinned labels (p.26)
--   - generalization: inverse temperature $\beta$ → every real $\beta$ in the expansion (54); reason: (54) is an identity of convergent power series for all $\beta$; it specializes to $\beta\ge0$
--   - reading: $f_t=\sum_{\vec b\in Q^{(t)}_{a^*}}\mu_{\vec b}P_{\vec b}$ with one product per sequence → a finite real combination $\sum_j\mu_jP_{L_j}$, each $L_j$ a reordering of a connected sequence $\vec b_j$; sequences may repeat; reason: the recursion produces both $P_aP_{\vec b}$ and $P_{\vec b}P_a$ from a commutator, and the count (71)–(72) bounds both; $\mu$ is real because the recursion has real coefficients
--   - encoding: $|\mathrm{supp}(P_{\vec b})|$ → the size of the union of the supports of the terms of $\vec b$; reason: the convention of (78); the support of the multiplied-out product is contained in it
--   - encoding: a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ with distinct non-identity Pauli strings → a coefficient function $c$ on Pauli words with $c(I)=0$, $A=\{P: c_P\neq 0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 8, eqs. (54)–(56), p.21

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_restrictTouching
import Definitions.Def_QThermalClassical_propagator
import Definitions.Def_QThermalClassical_IsConnectedSeq
import Definitions.Def_QThermalClassical_IsPauliProd

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 8 (Propagator expansion).** For an `(s, k)`-long-range Pauli Hamiltonian `H` and a
site set `K` of at most `k` qubits (for instance `K = supp(P_{a*})` for a label `a* ∈ A`),
`e^{−βH} e^{β(H − H_{(K)})} = Σ_{t≥0} (β^t/t!) f_t(H, H_{(K)})`, where `f_0 = I`,
`f_{t+1} = −[H, f_t] − f_t H_{(K)}`; and for every `t ≥ 1`, `f_t` is a real combination
`Σ_j μ_j P_{b⃗_j}` of products of the terms of connected sequences `b⃗_j ∈ Q^{(t)}_K` (each
product taken in some order of its factors), with `|supp(P_{b⃗})| ≤ kt` and
`Σ_j |μ_j| ≤ ∏_{i=1}^t (ks + 2ksi) ≤ (3ks)^t t!`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 8, eqs. (54)–(56), p.21.

**Formalization Note.** The paper's `a*` enters only through its site set, which may be any
`K` with `|K| ≤ k` (this covers the partially pinned labels of p.26). The family `(μ_j, b⃗_j)`
may repeat a sequence: the recursion produces both orders `P_a P_{b⃗}` and `P_{b⃗} P_a` of a
commutator, and the bound (56) counts both. `supp(P_{b⃗})` is the union of the supports of the
terms. -/
theorem lemma_8 {Q : Type} [Fintype Q] [DecidableEq Q] (s k : ℝ) (hs : 0 < s) (hk : 0 < k)
    (c : PauliWord Q → ℝ) (hc : IsLongRangePauli s k c) (K : Finset Q)
    (hK : (K.card : ℝ) ≤ k) :
    (∀ β : ℝ, HasSum (fun t : ℕ => (β ^ t / (t.factorial : ℝ)) •
        fSeq (ham c) (ham (touching c K)) t)
      (propagator (ham c) (ham (touching c K)) β)) ∧
    ∀ t : ℕ, 1 ≤ t → ∃ (N : ℕ) (μ : Fin N → ℝ) (b L : Fin N → List (PauliWord Q)),
      (∀ j, IsConnectedSeq c K (b j) ∧ (b j).length = t ∧ (L j).Perm (b j) ∧
        ((wordsSupport (b j)).card : ℝ) ≤ k * t) ∧
      fSeq (ham c) (ham (touching c K)) t = ∑ j, ((μ j : ℝ) : ℂ) • listProd (L j) ∧
      ∑ j, |μ j| ≤ ∏ i ∈ Finset.Icc 1 t, (k * s + 2 * k * s * i) ∧
      ∏ i ∈ Finset.Icc 1 t, (k * s + 2 * k * s * i) ≤ (3 * k * s) ^ t * (t.factorial : ℝ) := by sorry

end QThermalClassical
