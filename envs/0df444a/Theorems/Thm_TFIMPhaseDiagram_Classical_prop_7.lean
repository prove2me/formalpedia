-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_7
-- name    : TFIMPhaseDiagram.Classical.prop_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:04:09.105138+00:00
-- url     : https://prove2.me/theorems/64bb8f52-2eb1-42dd-bfe7-e7fc5a904d91
-- title:
--   Proposition 7 — Poisson paths discretize to the signed CBC cycle
-- statement:
--   Let $\eta\ge0$, $p\in\{0,1\}$ and $M\ge3$. Discretizing the parity-conditioned Poisson path at $0,1/M,\ldots,(M-1)/M$ gives exactly the closed-cycle Ising law with first $M-1$ couplings $K_M(\eta)=\frac12\log\coth(\eta/M)$ and last coupling $(-1)^pK_M(\eta)$:
--   $$\operatorname{Val}_{M\#}\nu_{\eta,p}=\pi_{K_{\eta,p},0}.$$
--   At zero the right side is the explicit limiting law. This identity connects continuous jump paths to the finite cycle sampler.
--
--   Differences from the source:
--   - encoding: path laws and limiting CBC law → jump data and explicit finite limiting mass; reason: Actual evaluations are preserved, including the eta=0 odd-parity branch.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.6 = PDF p.6, Proposition 7

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 7, p.6: includes the eta=0 limiting cycle law. -/
theorem prop_7 (M : ℕ) (hM : 3 ≤ M) (η : ℝ) (hη : 0 ≤ η) (p : Bool) :
  (pathLaw η p).map (discretize M) = pathCycleLaw (M := M) η p (fun _ => .finite 0) := by sorry
end TFIMPhaseDiagram.Classical
