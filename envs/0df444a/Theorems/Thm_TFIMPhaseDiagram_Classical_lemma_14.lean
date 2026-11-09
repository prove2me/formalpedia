-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_lemma_14
-- name    : TFIMPhaseDiagram.Classical.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:53.78012+00:00
-- url     : https://prove2.me/theorems/9b6ec97b-bbb9-423c-882e-b951fc584f3e
-- title:
--   Lemma 14 — Scaled cycle covariance operator norm
-- statement:
--   Let $\pi_{K,w}$ be the closed-cycle law on $M\ge3$ spins, allowing compatible infinite-field pins. Suppose $b>0$, $|K_k|\le b$, $\eta>0$, and $\tanh b=e^{-2\eta/M}$. Under the scaling $s\mapsto s/\sqrt M$,
--   $$\|\operatorname{Cov}(\widetilde\pi_{K,w})\|_{\mathrm{op}}\le\alpha_M(\eta)=\frac{\tanh\eta}{M\tanh(\eta/M)}.$$
--   This is the all-field covariance input to the entropy theorem; scaling the unscaled covariance norm by $1/M$ is exact.
--
--   Differences from the source:
--   - encoding: covariance of the push-forward by s/sqrt(M) → unscaled covariance operator norm divided by M; reason: Covariance scales quadratically; this is an exact identity, not a weaker bound. Infinite fields are compatible pins.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.8 = PDF p.8, Lemma 14

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Lemma 14, p.8; covariance of s/sqrt(M), all compatible infinite-field pins included. -/
theorem lemma_14 (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → Field)
    (hw : ∃ s, compatible w s) (b η : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hK : ∀ k, |K k| ≤ b) (hrel : Real.tanh b = Real.exp (-2*η/M)) :
  finiteCovNorm (cycleProb K w) / M ≤ alphaMesh M η := by sorry
end TFIMPhaseDiagram.Classical
