-- Prove2me | Theorems.Thm_SwitchingStable_Universal_Supplement_lemma_19
-- name    : SwitchingStable.Universal.Supplement.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:37:33.515761+00:00
-- url     : https://prove2.me/theorems/59c266d6-80b6-4be2-a1c1-413ac061969a
-- title:
--   Lemma 19 — canonical witnesses and both rotation endpoints
-- statement:
--   Let $I$ be any complete strict market, $\mu$ any stable matching, and $u$ a man with stable partners $v_0\succ_u\cdots\succ_u v_{d_u-1}$. Put $q=\operatorname{idx}_u(\mu)$. At every actual boundary $1\le j<d_u$, define $p_j=\mu^{-1}(v_{j-1})$ for $j\le q$ and $p_j=\mu^{-1}(v_j)$ for $j>q$. Then
--
--   $$p_j\in W^\mu_{u,j},\qquad p_j=p_k\ \Longrightarrow\ j=k.$$
--
--   The transition rotation $\rho_{u,j}$ exists and is unique. For every man $p\ne u$,
--
--   $$p\text{ or the woman }\mu(p)\text{ participates in }\rho_{u,j}\quad\Longrightarrow\quad p\in W^\mu_{u,j}.$$
--
--   The rotation is an actual exposed first-acceptable-below-current transition, followed by its elimination; it is not an arbitrary stable reassignment. This lemma supplies the canonical independent coordinate witnesses used by the finite-list estimate in Theorem 3, and retains the entire woman-endpoint participation clause. If $d_u=1$, there are no boundaries and all boundary assertions are vacuous as in the source.
--
--   Differences from the source:
--   - encoding: canonical witness selected separately according to j ≤ q or j > q → one piecewise canonical function, injective on the actual boundaries; reason: its two branches are exactly the displayed canonical witnesses
--   - encoding: the preceding paragraph identifies a unique transition rotation → existence and uniqueness of the exposure/elimination relation are included as conclusions; reason: keeps the source rotation meaningful without making existence a new hypothesis
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 35, PDF p. 36, Lemma 19; Section 6 and Appendices G–I

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_StableCertificates

namespace SwitchingStable.Universal.Supplement

open StableMatching

theorem lemma_19 {n : ℕ} (I : Instance n) (μ : Matching n) (hμ : I.IsStable μ)
    (u : Fin n) :
    (∀ j, 1 ≤ j → j < degree I u →
      canonical I μ u j ∈ exactWitness I μ u j) ∧
    (∀ j k, 1 ≤ j → j < degree I u → 1 ≤ k → k < degree I u →
      canonical I μ u j = canonical I μ u k → j = k) ∧
    (∀ j, 1 ≤ j → j < degree I u → ∃! ρ : StableCount.Rot n, Transition I u j ρ) ∧
    (∀ j, 1 ≤ j → j < degree I u → ∀ ρ : StableCount.Rot n, Transition I u j ρ →
      ∀ p : Fin n, p ≠ u →
      (manParticipates ρ p ∨ womanParticipates ρ (μ p)) → p ∈ exactWitness I μ u j) := by sorry

end SwitchingStable.Universal.Supplement
