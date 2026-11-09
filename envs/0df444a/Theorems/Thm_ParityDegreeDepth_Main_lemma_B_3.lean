-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_B_3
-- name    : ParityDegreeDepth.Main.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:57.8402+00:00
-- url     : https://prove2.me/theorems/81ddba61-7297-466b-984b-d52ce4b3803d
-- title:
--   Lemma B.3 — multiplicity grid inequality
-- statement:
--   Let $\mathbb F$ be any field, let $P\in\mathbb F[x_1,\ldots,x_n]$ be nonzero of total degree at most $D$, and let $S\subseteq\mathbb F$ be finite, possibly empty. Then
--   $$\sum_{a\in S^n}\operatorname{mult}_a P\le D|S|^{n-1}.$$
--
--   This bounds the sum of the individual multiplicities over an arbitrary finite grid, without requiring a finite coefficient field or a uniform vanishing order.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - generalization: the grid inequality with the proof beginning at n = 1 → all n ≥ 0, interpreting n - 1 as natural subtraction at n = 0; reason: at n = 0 a nonzero polynomial is a nonzero constant and its unique point has multiplicity zero, so the added case satisfies the same inequality
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma B.3, PDF page 23 / printed page 22.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def multiplicity {F : Type} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (a : Vec n F) : ℕ∞ :=
  ⨅ e ∈ (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support,
    (KakeyaHasse.order e : ℕ∞)


/-- lemma B 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_B_3 {F : Type} [Field F] {n D : ℕ} (P : MvPolynomial (Fin n) F)
    (hP : P ≠ 0) (hD : P.totalDegree ≤ D) (S : Finset F) :
    (∑ a : Fin n → S, multiplicity P (fun i => (a i : F))) ≤
      ((D * S.card ^ (n - 1) : ℕ) : ℕ∞) := by sorry

end ParityDegreeDepth.Main
