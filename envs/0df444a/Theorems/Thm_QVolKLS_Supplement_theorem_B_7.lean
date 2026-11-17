-- Prove2me | Theorems.Thm_QVolKLS_Supplement_theorem_B_7
-- name    : QVolKLS.Supplement.theorem_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:37:19.162214+00:00
-- url     : https://prove2.me/theorems/73c4f256-f728-4d25-a05d-f48872d08619
-- title:
--   Theorem B.7 — conductance and warm-start mixing of the lattice walk
-- statement:
--   Fix a covariance-comparison constant. There are positive absolute construction, conductance, mixing, quadrature, and mesh constants, depending only on that comparison constant, such that the following holds. Let $P_{\Lambda,A}$ be Algorithm 2 for a convex body and log-affine target, with $J$ proposal radii and preconditioner $A$ comparable to the continuous covariance. If the original and transformed cell-radius bounds, the derived exceptional-mass error, and conditions (66), (88), and (93) hold, and the finite direction sampler has error at most $1/100$, then for every $0<s<1/4$,
--   $$
--   \Phi_s(P_{\Lambda,A})\ge \frac{c\psi_D}{JD(1+\log(4/s))}.
--   $$
--   If the same conditions hold at $s=\eta/(2M)$, where $M\ge1$ and $0<\eta<1/2$, then every $M$-warm start mixes by some time $t$ satisfying
--   $$
--   t\le \frac{CJ^2D^2}{\psi_D^2}(1+\log(8M/\eta))^2\log(2M/\eta).
--   $$
--
--   This is the quantitative conductance-to-mixing estimate used to prove Theorem 5.2.
--
--   **Formalization Note** Conductance is the defining cut inequality for all sets with mass in $(s,1/2]$, avoiding a default infimum. The mixing conclusion supplies an actual natural time whose real coercion satisfies the displayed bound.
--
--   Differences from the source:
--   - encoding: the source defines $\Phi_s$ by an infimum and $\tau_{\mathrm{mix}}$ by a minimum → Lean states the equivalent cut inequalities and existence of an actual bounded natural time; reason: avoids Lean's default values for empty real infima while preserving every admissible cut and start
--   - encoding: the source writes $\psi_D$ in its reciprocal-KLS convention → Lean carries a positive real $\psi_D$ together with equality to the inverse of the published KLS constant `psiN D`; reason: makes the paper's convention explicit and prevents reversing the inequality
--   - encoding: the source works on the full cubic lattice and fixes Algorithm 2 in the preceding setup → Lean uses a finite two's-complement register required to cover the full lattice body and explicitly binds the rounded-ball sampler, geometric radius list, connector box, and transformed-radius bounds; reason: finite-register encoding of the same walk with no omitted lattice state or free proposal kernel
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Theorem B.7, pp.72-73, displays (97)-(98); conditions (66), (88), (93)

import Definitions.Def_QVolKLS_Supplement_LatticeWalk

set_option autoImplicit false

namespace QVolKLS.Supplement

open MeasureTheory
open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Theorem B.7
(Conductance and warm-start mixing)**, pp.72–73, displays (97)–(98), in the fixed-target setting
of Appendix B, pp.61–72.

For the preconditioned lattice Metropolis walk, the quadrature condition (66), tilt-mesh condition
(88), and separator mesh condition (93) imply the displayed `s`-conductance lower bound. When the
same conditions hold at `s = eta/(2M)`, every `M`-warm start mixes within the displayed bound.

The finite register is required to cover the complete lattice body, and the radius schedule,
rounded uniform-ball proposal, connector box, transformed cell radius, and transformed outer radius
are the objects fixed in Appendix B.2–B.3 rather than unrelated witness data.

**Formalization Note.** The covariance comparison constant `cCov` is fixed before all data; the
four constants hidden in the construction, conductance lower bound and mixing upper bound may
depend only on it. `ConductanceAtLeast` is the cut inequality defining `Φ_s`, avoiding a default
`sInf`. The cell-radius hypotheses are (64), `SatisfiesMeshError` records (79) and (82), and
`Satisfies66`, `Satisfies88`, and `Satisfies93` are literally (66), (88), and (93). The mixing
conclusion provides a natural time whose real coercion is
at most the printed real bound, so no ceiling weakens (98).
-/
theorem theorem_B_7 :
    ∀ cCov : ℝ, 1 ≤ cCov →
      ∃ (cCond Cmix Cquad cMesh Cradius Cerror : ℝ),
        0 < cCond ∧ 0 < Cmix ∧ 0 < Cquad ∧ 0 < cMesh ∧
          0 < Cradius ∧ 0 < Cerror ∧
        ∀ (D : ℕ), 1 ≤ D →
        ∀ (K : Set (Euc D)) (xc : Fin D → ℚ) (r0 R0 : ℚ) (tiltRat : Fin D → ℚ)
          (A : Matrix (Fin D) (Fin D) ℚ) (q : CommonWalkParams D)
          (W : LatticeWalk q K (ratPoint tiltRat) A)
          (psiD rho rhoA rMesh epsQuad epsMesh : ℝ),
          IsConvexBody K → Metric.ball (ratPoint xc) (r0 : ℝ) ⊆ K →
          K ⊆ Metric.closedBall (ratPoint xc) (R0 : ℝ) →
          0 < r0 → r0 ≤ R0 →
          RegCovers D q.b q.p (Metric.closedBall (ratPoint xc) (R0 : ℝ)) →
          ConnectorCovers q (R0 : ℝ) →
          TransformedOuterRadiusBound q K (ratPoint xc) W.WA →
          A.transpose = A →
          (∀ u : Euc D,
            cCov⁻¹ * dirVariance (logAffineMeasure K (ratPoint tiltRat)) u ≤ quadForm A u ∧
              quadForm A u ≤ cCov * dirVariance (logAffineMeasure K (ratPoint tiltRat)) u) →
          0 < psiD → ENNReal.ofReal psiD = (SongZhangKLS.psiN D)⁻¹ →
          ((2 : ℝ)⁻¹ ^ q.p) * Real.sqrt D / 2 ≤ rho →
          rho ≤ ((2 : ℝ)⁻¹ ^ q.p) * Real.sqrt D →
          TransformedCellRadiusBound q W.WA rhoA →
          Satisfies66 Cquad D (r0 : ℝ) (R0 : ℝ) ‖ratPoint tiltRat‖ rho epsQuad →
          SatisfiesMeshError Cradius Cerror D rhoA epsQuad rMesh epsMesh →
          rMesh = q.rMesh →
          Satisfies88 ‖ratPoint tiltRat‖ rho → 0 ≤ W.epsDir → W.epsDir ≤ 1 / 100 →
          0 ≤ epsMesh →
          (∀ s : ℝ, 0 < s → s < 1 / 4 → Satisfies93 cMesh D psiD s epsMesh →
            ConductanceAtLeast (walkOmega q K) (walkLaw q K (ratPoint tiltRat)) W.P s
              (cCond * psiD / ((q.J : ℝ) * (D : ℝ) * (1 + Real.log (4 / s))))) ∧
          (∀ M eta : ℝ, 1 ≤ M → 0 < eta → eta < 1 / 2 →
            Satisfies93 cMesh D psiD (eta / (2 * M)) epsMesh →
            ∃ t : ℕ,
              (t : ℝ) ≤ Cmix * ((q.J : ℝ) ^ 2 * (D : ℝ) ^ 2 / psiD ^ 2) *
                (1 + Real.log (8 * M / eta)) ^ 2 * Real.log (2 * M / eta) ∧
              MixTimeWarmLe (walkOmega q K) M eta (walkLaw q K (ratPoint tiltRat)) W.P t) := by sorry

end QVolKLS.Supplement
