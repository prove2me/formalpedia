-- Prove2me | Theorems.Thm_SubsetConvFPRAS_lemma_5_5
-- name    : SubsetConvFPRAS.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:40.616217+00:00
-- url     : https://prove2.me/theorems/89d42f2f-c33c-49aa-b10e-25848e22d8ff
-- title:
--   Lemma 5.5 — the exchange chain on the bases pair law has spectral gap at least $1$
-- statement:
--   Assume the standing hypotheses of §5: $\mu,\nu\ge0$ supported on $\binom Ua$ and $\binom Ub$ with $a+b=n=|U|\ge1$, and $g_\mu,g_\nu$ log-concave. Let $t\in(0,1]^U$, $z\in\mathbb R^U_{>0}$, and let $\pi_{t,z}(S,T)\propto\mu(S)\nu(T)t^{S\cap T}z^Sz^T$ be the bases pair law. On $\operatorname{supp}\pi_{t,z}$ consider the exchange chain with rates
--   $$q\bigl((S,T),(S-u+v,T)\bigr)=t_u^{-\mathbf 1[u\in T]}\frac{z_v\,\mu(S-u+v)}{\sum_{w\in U\setminus(S-u)}z_w\,\mu(S-u+w)}\qquad(u\in S,\ v\notin S),\tag{19}$$
--   the rates updating $T$ obtained by interchanging $(S,\mu)$ and $(T,\nu)$, and all other off-diagonal rates zero. This chain is reversible with respect to $\pi_{t,z}$ and
--   $$\operatorname{Var}_{\pi_{t,z}}[f]\le\mathcal E_q(f,f)\qquad\text{for all }f:\operatorname{supp}\pi_{t,z}\to\mathbb R.\tag{20}$$
--
--   This chain can be run with the original value oracles; it is the sampler behind Corollary 5.6, and its gap is the $\gamma=1$ of Lemma 2.5.
--
--   Differences from the source:
--   - encoding: the chain on supp π_{t,z} → the support as a subtype, with the rates (19) restricted to it; reason: same state space and rates
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Definition 5.4 and Lemma 5.5, p.21 (proof p.23)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_PairLaws

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Lemma 5.5, p.21. Under the standing hypotheses of §5, for
every `t ∈ (0,1]^U` and `z ∈ ℝ^U_{>0}`, the exchange chain (19) on `supp π_{t,z}` is reversible with respect to
the bases pair law `π_{t,z}`, and `Var_{π_{t,z}}[f] ≤ E_q(f,f)`, (20).

**Formalization Note.** The standing hypotheses of §5 are `IsHomogeneousPair`; under them `softLaw` is the
bases pair law of Definition 5.4. The state space is the support of `π_{t,z}` as a subtype, and the rates (19) are
restricted to it. The penalty `t` is a vector. -/
theorem lemma_5_5 {U : Type} [Fintype U] [DecidableEq U] (a b : ℕ) (μ ν : Finset U → ℝ)
    (h : IsHomogeneousPair a b μ ν) (t z : U → ℝ) (ht : ∀ u, 0 < t u ∧ t u ≤ 1)
    (hz : ∀ u, 0 < z u) :
    IsReversibleChain (onSupp (softLaw μ ν t z))
        (onSuppRate (softLaw μ ν t z) (exchangeRate μ ν t z)) ∧
      HasPoincare (onSupp (softLaw μ ν t z))
        (onSuppRate (softLaw μ ν t z) (exchangeRate μ ν t z)) 1 := by sorry

end SubsetConvFPRAS
