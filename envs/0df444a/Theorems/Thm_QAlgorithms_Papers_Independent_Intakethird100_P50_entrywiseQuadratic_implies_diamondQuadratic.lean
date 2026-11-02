-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_entrywiseQuadratic_implies_diamondQuadratic
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.entrywiseQuadratic_implies_diamondQuadratic
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:52:05.284771+00:00
-- url     : https://prove2.me/theorems/ad641272-80d7-4903-8fcf-1ff0bf71984a
-- title:
--   Corollary 2: entrywise quadratic Choi errors imply quadratic diamond error
-- statement:
--   Fix nonzero finite-dimensional complex Hilbert spaces $A,B$ and bases. Let $\Theta(p):\mathcal B(A)\to\mathcal B(B)$ be complex-linear for every real $p$. Suppose that, for each pair of indices $u,v$ of the unnormalized reference-first Choi matrix, there exist $C_{uv}\ge0$ and $\delta_{uv}>0$ such that $|J(\Theta(p))_{uv}|\le C_{uv}p^2$ whenever $0<|p|<\delta_{uv}$. Then there exist $C\ge0$ and $\delta>0$ such that
--   $$
--   \|\Theta(p)\|_\diamond\le Cp^2\qquad(0<|p|<\delta).
--   $$
--   This is a two-sided local statement; finite fixed dimensions allow common constants for the entries.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 6, Corollary 2: entrywise quadratic Choi errors imply quadratic diamond error

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)

open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- Corollary 2, PDF p.6: a two-sided punctured neighborhood of zero; dimensions
and bases are fixed. Each entry may initially have its own big-O constants. -/
theorem entrywiseQuadratic_implies_diamondQuadratic [Nonempty A] [Nonempty B]
    (Theta : ℝ → (Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ))
    (h : ∀ i j : A × B, ∃ C : ℝ, 0 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ p : ℝ, 0 < |p| → |p| < delta → ‖choi (Theta p) i j‖ ≤ C * p ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ p : ℝ, 0 < |p| → |p| < delta → diamond (Theta p) ≤ C * p ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
