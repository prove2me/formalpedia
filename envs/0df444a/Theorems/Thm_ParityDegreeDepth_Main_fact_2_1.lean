-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_fact_2_1
-- name    : ParityDegreeDepth.Main.fact_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:53.389473+00:00
-- url     : https://prove2.me/theorems/d32dfffa-9c3c-4e49-b64c-41122f2c95ed
-- title:
--   Fact 2.1 — products and translations
-- statement:
--   For real functions $f,g$ on $\mathbb F_2^n$, with the normalized Walsh transform and convolution on the frequency group,
--   $$\widehat{fg}(\xi)=\sum_\eta\widehat f(\eta)\widehat g(\xi+\eta),\qquad \|\widehat{fg}\|_1\le\|\widehat f\|_1\|\widehat g\|_1.$$
--   For every translation $a$ and character $\chi_a$, both $f(\cdot+a)$ and $f\chi_a$ have the same spectral norm as $f$.
--
--   These identities give the product and translation rules for finite-cube Fourier analysis.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: convolution on the binary frequency group → a finite sum at ξ + η; reason: addition and subtraction coincide over F₂
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Fact 2.1, PDF page 5 / printed page 4.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def character {n : ℕ} (a x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (∑ i, a i * x i).val

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|


/-- fact 2 1; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem fact_2_1 {n : ℕ} (f g : Vec n (ZMod 2) → ℝ) :
    (∀ ξ, QAlgorithms.boolFourier (fun x => f x * g x) ξ =
      ∑ η, QAlgorithms.boolFourier f η * QAlgorithms.boolFourier g (ξ + η)) ∧
    spectralNorm (fun x => f x * g x) ≤ spectralNorm f * spectralNorm g ∧
    (∀ a, spectralNorm (fun x => f (x + a)) = spectralNorm f) ∧
    (∀ a, spectralNorm (fun x => f x * character a x) = spectralNorm f) := by sorry

end ParityDegreeDepth.Main
