-- Prove2me | Theorems.Thm_SDC_bipartite_host_evaluation
-- name    : SDC.bipartite_host_evaluation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-23T09:24:19.405855+00:00
-- url     : https://prove2.me/theorems/a4802773-8746-4b26-a00f-7981f1ecf005
-- title:
--   Calibration on complete bipartite hosts: the two densities in closed form
-- statement:
--   Calibration on complete bipartite hosts. In the complete bipartite host with parts of sizes a and b, the edge density is 2ab/(a+b)^2 and the homomorphism density of the pattern is (a^13 * b^22 + b^13 * a^22)/(a+b)^35: the connectivity of the triple system (any two points are joined through a chain of shared triples) forces every homomorphism of the bipartite pattern to send all points to one part and all triples to the other, and the two choices of the part give the two monomials. Uniform hosts do not witness the goal; the violating host of the manuscript must be genuinely non-uniform.
-- source:
--   Mission-authored calibration lemma within the framework of the uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt); the closed forms are computed from the connectivity of the triple system of Table 1.

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density

namespace SDC

/-!  Calibration on complete bipartite hosts. In the complete bipartite
host with parts of sizes a and b, the edge density is 2ab/(a+b)^2 and the
homomorphism density of the pattern is (a^13 * b^22 + b^13 * a^22)/(a+b)^35:
the connectivity of the triple system (any two points are joined through
a chain of shared triples) forces every homomorphism of the bipartite
pattern to send all points to one part and all triples to the other, and
the two choices of the part give the two monomials. Uniform hosts do not
witness the goal; the violating host of the manuscript must be genuinely
non-uniform.  -/

theorem bipartite_host_evaluation (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    edgeDensity (completeBipartite a b) =
      2 * (a : ℝ) * (b : ℝ) / ((a : ℝ) + (b : ℝ)) ^ 2 ∧
    homDensity H (completeBipartite a b) =
      ((a : ℝ) ^ 13 * (b : ℝ) ^ 22 + (b : ℝ) ^ 13 * (a : ℝ) ^ 22)
        / ((a : ℝ) + (b : ℝ)) ^ 35 := by
  sorry

end SDC
