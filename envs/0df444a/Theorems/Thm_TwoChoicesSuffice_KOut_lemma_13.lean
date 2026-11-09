-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_13
-- name    : TwoChoicesSuffice.KOut.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:16.769019+00:00
-- url     : https://prove2.me/theorems/01e1bae3-4b5a-4713-a273-1eaeab3e35c5
-- title:
--   Lemma 13 — two-out crossing edges versus the relevant-degree potential
-- statement:
--   Let $G$ be a finite simple graph. Under the marked two-out law (a uniform two-choice outcome $\sigma$ with replacement and, conditional on $H^1_G(\sigma)$, a uniformly random proper $10$-colouring with zero set $S$), let $B^+=B^+(\sigma,S)$ be the augmented base graph and $\Phi_R$ the relevant-degree component potential, leaders taken by increasing $d_v$ with ties broken by a fixed order $\pi$. Then
--   $$
--   \frac1{14}\,\mathbb E\bigl[x_G(H^2_G)\bigr]\le\frac{241}{80}\,\mathbb E\bigl[\Phi_R(B^+)\bigr].
--   $$
--
--   With Lemma 15 this yields Theorem 12.
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: a fixed total order π chosen independently of the sample and colouring → the LinearOrder instance of V, universally quantified; reason: a fixed deterministic order is independent of the randomness; every choice of π is covered
--   - encoding: E[x_G(H^2_G)] taken in the joint law of (σ, S) → E[x_G(H^2_G)] taken in the two-out law of σ alone; reason: x_G(H^2_G) depends only on σ, whose marginal under the joint law is the two-out law
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 13, printed p. 16, PDF p. 17

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Potentials
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders
import Definitions.Def_TwoChoicesSuffice_KOut_Coloring
import Definitions.Def_TwoChoicesSuffice_KOut_Marked

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 13 (PDF p. 17, printed p. 16). For any simple graph `G`,
`(1/14) E[x_G(H^2_G)] ≤ (241/80) E[Φ_R(B⁺)]`, where the right-hand expectation is under the
marked two-out law (uniform two-choice outcome `σ`, then a uniform proper 10-colouring of
`H^1_G(σ)` with zero set `S`), `B⁺ = B⁺(σ, S)` is the augmented base graph and `Φ_R` the
relevant-degree component potential (leaders for increasing `d_v`, ties by the fixed
order `π` of `V`). -/
theorem lemma_13 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    (1 / 14 : ℝ) * kOutExpect G 2 (fun σ => (crossingCount G (prefixGraph G σ 2) : ℝ)) ≤
      (241 / 80 : ℝ) * markedExpect G (fun σ S => (relPotential G σ S (augBase G σ S) : ℝ)) := by sorry

end TwoChoicesSuffice.KOut
