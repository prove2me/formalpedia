-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_one_way_tests_limited_disturbance
-- name    : QAlgorithms.Papers.Independent.Support50.P16.one_way_tests_limited_disturbance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:01:18.499613+00:00
-- url     : https://prove2.me/theorems/5d38c377-f896-45fc-bfb9-8aaf0615c3b6
-- title:
--   Lemma 5, Eqs. (11)–(12): one-way tests with limited disturbance
-- statement:
--   Let $\rho_{ABE},\sigma_{ABE}$ be any normalized states on nonzero finite-dimensional registers. Let $M^{AB\to X}$ be any normalized one-way LOCC measurement with communication from $A$ to $B$. There is one sequence of instruments $T_n^{A^nB^n\to YB^n}$, with a fixed binary classical register $Y$, implementable by Alice's measurement, communication of her result to Bob, and Bob's conditional quantum instrument, such that
--
--   $$
--   \begin{aligned}
--   \lim_{n\to\infty}\frac1nD(T_n^c(\rho_{AB}^{\otimes n})\Vert T_n^c(\sigma_{AB}^{\otimes n}))
--    &=D(M(\rho_{AB})\Vert M(\sigma_{AB})),\\
--   \lim_{n\to\infty}\bigl\|(T_n^q\otimes\mathrm{id}_{E^n})(\rho_{ABE}^{\otimes n})-\rho_{BE}^{\otimes n}\bigr\|_1&=0.
--   \end{aligned}
--   $$
--
--   Here $T_n^c=\operatorname{Tr}_{B^n}\circ T_n$, $T_n^q=\operatorname{Tr}_Y\circ T_n$, and both reduced input states are actual partial traces. Relative entropy is in bits and may be infinite; the second limit uses the full trace norm. The instrument has no access to $E$. Its binary output is the source proof's concrete hypothesis-test realization; the input measurement's output alphabet remains arbitrary. Only $\rho$ is required to remain undisturbed on $BE$.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 6, Lemma 5, Eqs. (11)–(12): one-way tests with limited disturbance

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

namespace QAlgorithms.Papers.Independent.Support50.P16

noncomputable section

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "tau" => QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed

local notation "RE" => QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement

local notation "RER" => QAlgorithms.Papers.Independent.Information100.P54.regularizedEntanglement

local notation "SQ" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "CMI" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "MI" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "LOCC" => QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC

local notation "power" => QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower

local notation "index" => QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex

-- Accepted matrix coordinates (not P50.Bipartite, which is a vector space).

local notation "Bipartite" => QAlgorithms.Papers.Independent.Dependency50.P50.BipartiteMat

-- Positive outcome counts follow already from a POVM on a nonzero register.

local notation "FiniteMeasurement" => QAlgorithms.Papers.Independent.Information100.P04.Measurement

local notation "relative" =>
  ((fun _ _ rho => RE rho) : ExtendedEntanglementFunctional)

-- Reuse the accepted operational/variational quantity through a typed notation.

local notation "squashed" =>
  ((fun _ _ rho => ENNReal.ofReal (SQ rho)) : ExtendedEntanglementFunctional)

local notation "originalMarginal" => QAlgorithms.Papers.Independent.Information100.P04.principalMarginal

-- Exact accepted partial trace of the same AA'BB' extension.

local notation "ancillaryMarginal" => QAlgorithms.Papers.Independent.Information100.P04.ancillaryMarginal

local notation "distillable" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Gap48.P32.twoWayDistillable rho)) : ExtendedEntanglementFunctional)

local notation "cost" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost
    (fun _ _ X Y => traceNorm (X-Y)) rho)) : ExtendedEntanglementFunctional)

/-- Lemma 5, Eqs.(11)--(12), PDF p.6; constructive proof pp.6--8.
ONE binary instrument sequence has both limits. Only rho is preserved.
The spectator E is untouched coherently; there is no support-inclusion assumption. -/
theorem one_way_tests_limited_disturbance {a b e : ℕ+}
    (rho sigma : Matrix ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ))
      ((Fin (a : ℕ) × Fin (b : ℕ)) × Fin (e : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (M : FiniteMeasurement (Fin (a : ℕ) × Fin (b : ℕ))) (hM : IsAliceToBobPOVM M) :
    ∃ T : (r : ℕ) → OneWayRetainedInstrument (copyDimension a (r+1)) (copyDimension b (r+1)),
      Tendsto (fun r => finiteKLBits
        (retainedClassical (T r) (power (traceRight rho) (r+1)))
        (retainedClassical (T r) (power (traceRight sigma) (r+1))) / (r+1 : ℝ≥0∞))
        atTop (nhds (finiteKLBits
          (povmOutcomeLaw M (traceRight rho)) (povmOutcomeLaw M (traceRight sigma)))) ∧
      Tendsto (fun r =>
        let BEIndex := Fin ((b : ℕ)^(r+1)) × Fin ((e : ℕ)^(r+1))
        let disturbed : Matrix BEIndex BEIndex ℂ :=
          QAlgorithms.Papers.Independent.Dependency50.P19.first (retainedQuantum (T r))
            (extensionCopies rho (r+1))
        let target : Matrix BEIndex BEIndex ℂ :=
          power (traceLeft (QAlgorithms.Papers.Independent.Dependency50.P19.associate rho)) (r+1)
        traceNorm (disturbed - target))
        atTop (nhds 0) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
