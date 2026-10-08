-- Prove2me | Theorems.Thm_PrimalDualLDR_Multistage_lemma_3
-- name    : PrimalDualLDR.Multistage.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:34.176792+00:00
-- url     : https://prove2.me/theorems/eae5d54f-471a-4232-9ce7-c6b09dd8b770
-- title:
--   Lemma 3 — the non-anticipative slack constraint (4.5b) is equivalent to its full-information form (4.5c)
-- statement:
--   Consider the multistage setting of §4 under its standing assumptions and the linear-conditional-mean assumption $\mathbb E_t(\xi) = M_tP_t\xi$ $\mathbb P$-a.s., with $M = \mathbb E(\xi\xi^\top)$. Fix a stage $t$ and a matrix $S_t \in \mathbb R^{m_t\times k^t}$. Then the constraint
--   $$\exists\, s_t \in \mathcal L^2_{k^t,m_t} : \ \mathbb E\big(s_t(\xi^t)\,\xi^\top\big) = S_tP_tM, \quad s_t(\xi^t) \ge 0 \ \ \mathbb P\text{-a.s.} \tag{4.5b}$$
--   is equivalent to
--   $$\exists\, \tilde s_t \in \mathcal L^2_{k,m_t} : \ \mathbb E\big(\tilde s_t(\xi)\,\xi^\top\big) = S_tP_tM, \quad \tilde s_t(\xi) \ge 0 \ \ \mathbb P\text{-a.s.} \tag{4.5c}$$
--
--   In (4.5b) the slack is non-anticipative (a function of the history $\xi^t$), while in (4.5c) it may depend on the whole of $\xi$. The equivalence makes the one-stage cone description of Proposition 3 applicable to the slack constraints of $\mathcal{MSP}^l$.
--
--   **Formalization Note** The page prints the sign condition of (4.5c) as "$\tilde s_t(\xi^t) \ge 0$" for a function of the full $\xi$; it is read as $\tilde s_t(\xi) \ge 0$. Moment matrices are entrywise Bochner integrals.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 21, Lemma 3, (4.5b), (4.5c)

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

/-- Lemma 3 (p. 21): under the standing assumptions of §4 and the linear-conditional-mean assumption,
for any given `S_t ∈ ℝ^{m_t × k^t}`, constraint (4.5b) — there is a non-anticipative
`s_t ∈ 𝓛²_{k^t,m_t}` with `𝔼(s_t(ξ^t) ξᵀ) = S_t P_t M` and `s_t(ξ^t) ≥ 0` `P`-a.s. — is equivalent to
(4.5c) — there is `s̃_t ∈ 𝓛²_{k,m_t}`, a function of the whole `ξ`, with `𝔼(s̃_t(ξ) ξᵀ) = S_t P_t M` and
`s̃_t(ξ) ≥ 0` `P`-a.s. -/
theorem lemma_3 (σ : Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T)
    (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ) :
    (∃ s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ), σ.IsL2RuleAt t s ∧
      σ.moment t s = S * σ.Pt t * σ.M ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ s (σ.tr t ξ) i) ↔
    (∃ st : (Fin σ.k → ℝ) → (Fin (σ.m t) → ℝ), PrimalDualLDR.FixedRecourse.IsL2Rule σ.P st ∧
      (fun i j => ∫ ξ, st ξ i * ξ j ∂σ.P) = S * σ.Pt t * σ.M ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ st ξ i) := by sorry

end PrimalDualLDR.Multistage
