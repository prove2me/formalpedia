-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_entropy_balance
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.entropy_balance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:17:12.65901+00:00
-- url     : https://prove2.me/theorems/1e000aa0-2cb6-48d1-ab0a-247d0b4549b1
-- title:
--   §3.4(a)–(c) — nonnegative convex entropy production and balance
-- statement:
--   Assume only the specified detailed-balance decomposition on $B(\mathbb C^d)$, $d>0$. Use the signed relative entropy $\operatorname{Ent}(\rho\mid\nu)=\operatorname{tr}(\rho(\log\nu-\log\rho))$ for faithful $\nu$ and von Neumann entropy $\operatorname{Ent}(\rho)=-\operatorname{tr}(\rho\log\rho)$. Entropy production is the sum of right derivatives at zero of $\operatorname{Ent}(e^{tL_j^*}(\rho)\mid\rho_j)$. These right derivatives and the total entropy's right derivative exist in the extended real line; singular input states may give $+\infty$.
--
--   Each reservoir's signed relative entropy is nondecreasing on nonnegative time. The map $\rho\mapsto\sigma(\rho)$ is nonnegative and convex on the entire state space. With $S_j=-\log\rho_j$ and $I_j=L_j(S_j)$,
--
--   $$\left.\frac{d}{dt}\operatorname{Ent}(e^{tL^*}(\rho))\right|_{0+}=\sigma(\rho)+\sum_j\rho(I_j).$$
--
--   For stationary $\rho$, $\sigma(\rho)=-\sum_j\rho(I_j)$. Faithful input states have finite entropy production. No ER, TR, or thermal hypothesis is used. The balance identifies the reservoir entropy fluxes.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 10, §3.4(a)–(c)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF pp.9–10, Section 3.4(a)–(c): signed relative entropy is monotone, entropy production
is nonnegative and convex, and the entropy balance holds with extended right derivatives. -/
theorem entropy_balance {d M : ℕ} (D : DBData d M) :
    (∀ rho, IsDensityMatrix rho → ∀ j,
      Tendsto (fun t : ℝ => (((finiteRelativeEntropyNats (hsAdjoint (qdsEvolution (D.generator j) t) rho) (D.rho j) -
        finiteRelativeEntropyNats rho (D.rho j)) / t : ℝ) : EReal))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (rightDerivative (fun t => finiteRelativeEntropyNats (hsAdjoint (qdsEvolution (D.generator j) t) rho) (D.rho j))))) ∧
    (∀ rho, IsDensityMatrix rho →
      Tendsto (fun t : ℝ => (((entropy (hsAdjoint (qdsEvolution (reservoirGenerator D) t) rho) - entropy rho) / t : ℝ) : EReal))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (rightDerivative (fun t => entropy (hsAdjoint (qdsEvolution (reservoirGenerator D) t) rho))))) ∧
    (∀ rho, IsDensityMatrix rho → ∀ j, MonotoneOn
      (fun t : ℝ => finiteRelativeEntropyNats (hsAdjoint (qdsEvolution (D.generator j) t) rho) (D.rho j)) (Set.Ici 0)) ∧
    (∀ rho, IsDensityMatrix rho → 0 ≤ reservoirEntropyProduction D rho) ∧
    (∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma → ∀ r : ℝ, 0 < r → r < 1 →
      reservoirEntropyProduction D ((r : ℂ) • rho + ((1 - r : ℝ) : ℂ) • sigma) ≤
        (r : EReal) * reservoirEntropyProduction D rho + ((1 - r : ℝ) : EReal) * reservoirEntropyProduction D sigma) ∧
    (∀ rho, IsDensityMatrix rho →
      rightDerivative (fun t => entropy (hsAdjoint (qdsEvolution (reservoirGenerator D) t) rho)) =
        reservoirEntropyProduction D rho + ((∑ j, evaluate rho (entropyFlux D j) : ℝ) : EReal)) ∧
    (∀ rho, IsDensityMatrix rho → StationaryDensity (reservoirGenerator D) rho →
      reservoirEntropyProduction D rho = ((-∑ j, evaluate rho (entropyFlux D j) : ℝ) : EReal)) ∧
    (∀ rho, Faithful rho → reservoirEntropyProduction D rho ≠ ⊤ ∧ reservoirEntropyProduction D rho ≠ ⊥) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
