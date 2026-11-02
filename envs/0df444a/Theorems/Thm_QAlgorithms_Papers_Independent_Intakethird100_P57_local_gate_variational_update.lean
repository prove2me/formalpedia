-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_local_gate_variational_update
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.local_gate_variational_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:15:37.459587+00:00
-- url     : https://prove2.me/theorems/8dd1acfe-de77-4ac2-bccc-aa7284530773
-- title:
--   Circuit simulation: local coordinate updates for the overlap objective
-- statement:
--   Let $N,D\ge1$. Normalize a nonzero initial RAGE vector with $V=I$ and apply a single-qubit unitary at site $q$, giving the unit target $\chi$. Fix admissible nonzero trial data with the same nonincident edges, and vary one trial site tensor pair. Let $L$ be its physical-state map, $G=L^\dagger L$, and $b=L^\dagger\chi$. The normal equations
--
--   $$Gx=b$$
--
--   have a solution. Every solution gives the orthogonal projection $Lx$ of $\chi$ onto $\operatorname{range}L$. If $Lx\ne0$, it maximizes $|\langle Ly,\chi\rangle|^2/\|Ly\|^2$ over all nonzero trial vectors; if $Lx=0$, all such objectives equal zero. Singular $G$ is allowed.
--
--   With the trial tensors fixed, varying one edge incident on $q$ keeps the norm squared $Z$ constant and gives
--
--   $$\mathcal O(z)=\frac{c_0+2\operatorname{Re}(c_1z)}Z,\qquad |z|=1,$$
--
--   with coefficients explicitly obtained from the complementary edge components. A maximum on this circle is attained. These are coordinate optima in an alternating sweep, with all other edges frozen.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 4, Circuit simulation: local coordinate updates for the overlap objective

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Eq.(5) and following paragraph: coordinate optima in an alternating sweep.
The singular normal equations and zero-projection case are retained. Nonincident edges are
frozen by edgeTrial. The statement makes no claim of global convergence of the sweep. -/
theorem local_gate_variational_update {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A Atr : Tensors N D) (G Gtr : PhaseGraph N) (hv : traceMPS A ≠ 0)
    (htrial : traceMPS Atr ≠ 0) (q : Fin N) (U : Matrix.unitaryGroup Bool ℂ)
    (hfixed : ∀ i j, i ≠ q → j ≠ q → Gtr.weight i j = G.weight i j) (k : Fin N) :
    let chi := act (localGate q U) (normalizeRageVector (rage A G (fun _ => 1)))
    let L := siteMap Atr Gtr (fun _ => 1) k
    let G := L.conjTranspose * L
    let b := L.conjTranspose.mulVec (WithLp.ofLp chi)
    (∃ x : SiteCoordinates D → ℂ, G.mulVec x = b) ∧
    (∀ x : SiteCoordinates D → ℂ, G.mulVec x = b →
      (∀ y : SiteCoordinates D → ℂ,
        inner ℂ (siteVector L y) (chi - siteVector L x) = 0) ∧
      (siteVector L x ≠ 0 → ∀ y : SiteCoordinates D → ℂ, siteVector L y ≠ 0 →
        overlapObjective (siteVector L y) chi ≤ overlapObjective (siteVector L x) chi) ∧
      (siteVector L x = 0 → ∀ y : SiteCoordinates D → ℂ, siteVector L y ≠ 0 →
        overlapObjective (siteVector L y) chi = 0)) ∧
    (∀ j : Fin N, j ≠ q →
      let c := overlapCoefficients Atr Gtr q j chi
      let Z := ‖traceMPS Atr‖ ^ 2
      (∀ z : ℂ, ‖z‖ = 1 →
        overlapObjective (edgeTrial Atr Gtr (fun _ => 1) q j z) chi =
          (c.1 + 2 * (c.2 * z).re) / Z) ∧
      (∃ z : ℂ, ‖z‖ = 1 ∧ ∀ w : ℂ, ‖w‖ = 1 →
        overlapObjective (edgeTrial Atr Gtr (fun _ => 1) q j w) chi ≤
          overlapObjective (edgeTrial Atr Gtr (fun _ => 1) q j z) chi)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
