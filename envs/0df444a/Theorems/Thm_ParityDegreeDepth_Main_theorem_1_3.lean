-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_theorem_1_3
-- name    : ParityDegreeDepth.Main.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:54.166519+00:00
-- url     : https://prove2.me/theorems/8ef71530-4b35-423a-9109-2d3e608c778e
-- title:
--   Theorem 1.3 — complete explicit depth and communication bounds
-- statement:
--   There is an absolute constant $C>0$, independent of $n$, $d$, and $p$, such that every phase $f=(-1)^p$ of exact algebraic normal-form degree $d\ge2$ on $\mathbb F_2^n$ satisfies the complete chain
--   $$D_\oplus(f)\le1+\frac{2^{2d-1}-5}{3}\log_2\|\widehat f\|_1\le1+\frac{2^{2d-1}-5}{6}\log_2s(f).$$
--   For the XOR function $F(x,y)=f(x+y)$ one also has
--   $$\tfrac12D^{\rm cc}(F)\le1+\frac{2^{2d-1}-5}{6}\log_2s(f),\qquad D^{\rm cc}(F)\le2D_\oplus(f),$$
--   and the dimension- and degree-uniform consequences
--   $$D_\oplus(f)\le C4^d\log_2s(f),\qquad\tfrac12D^{\rm cc}(F)\le C4^d\log_2s(f).$$
--   Both depths minimize the worst-case costs of actual finite exact computing trees or deterministic public-output binary protocols. The same middle expression appears in the two comparisons.
--
--   This is the paper's main explicit spectral-norm and sparsity bound, including its concluding communication consequence.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: the final O(4^d log₂ s(f)) assertions and the reference to Eq. (2) → one positive constant quantified before n, d, p, together with the explicit half-communication estimate and Eq. (2); reason: the uniform inequalities express precisely the stated asymptotic consequences without changing either explicit coefficient
--   - encoding: minimum exact parity and communication depths of signs → natural infima over actual computing trees and published public-output bit protocols with true corresponding to -1; reason: every phase has a coordinate tree and a simulated computing protocol, as checked in the operational verification module
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Theorem 1.3, PDF page 3 / printed page 2 Eq. (2), PDF 2 / printed 1.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

private def sparsity {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

private def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private inductive ParityTree (n : ℕ) where
  | leaf (b : Bool)
  | query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (zero one : ParityTree n)

private def treeDepth {n : ℕ} : ParityTree n → ℕ
  | .leaf _ => 0
  | .query _ _ l r => 1 + max (treeDepth l) (treeDepth r)

private def treeEval {n : ℕ} : ParityTree n → Vec n (ZMod 2) → ℝ
  | .leaf b, _ => if b then -1 else 1
  | .query a _ l r, x => if ∑ i, a i * x i = 0 then treeEval l x else treeEval r x

private def parityDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = f x}

private def protocolSign {n : ℕ} (t : DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2)))
    (x y : Vec n (ZMod 2)) : ℝ := if t.eval x y then -1 else 1

private def communicationDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2)),
    t.depth = k ∧ ∀ x y, protocolSign t x y = f (x + y)}


/-- theorem 1 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem theorem_1_3:
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
    2 ≤ d → anfDegree p = (d : WithBot ℕ) →
    (parityDepth (phase p) : ℝ) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ∧
    1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 3 * logTwo (spectralNorm (phase p)) ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤
      1 + ((2 : ℝ) ^ (2 * d - 1) - 5) / 6 * logTwo (sparsity (phase p)) ∧
    communicationDepth (phase p) ≤ 2 * parityDepth (phase p) ∧
    (parityDepth (phase p) : ℝ) ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) ∧
    (communicationDepth (phase p) : ℝ) / 2 ≤ C * (4 : ℝ) ^ d * logTwo (sparsity (phase p)) := by sorry

end ParityDegreeDepth.Main
