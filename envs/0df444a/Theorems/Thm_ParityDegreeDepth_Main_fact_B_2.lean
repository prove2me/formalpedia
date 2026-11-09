-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_fact_B_2
-- name    : ParityDegreeDepth.Main.fact_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:20.716962+00:00
-- url     : https://prove2.me/theorems/054de3da-1030-45e1-958f-87d868ded5df
-- title:
--   Fact B.2 — multiplicity under derivatives and lines
-- statement:
--   Let $\mathbb F$ be any field, let $P\in\mathbb F[x_1,\ldots,x_n]$, let $e$ be a nonnegative exponent multi-index of total order $|e|$, and let $a\in\mathbb F^n$. With Hasse derivatives and multiplicity $+\infty$ for the zero polynomial,
--   $$\operatorname{mult}_a(P^{(e)})\ge\operatorname{mult}_a(P)-|e|.$$
--   For every nonzero direction $v$ defining a line through $a$, if $P(a+tv)$ is not the zero univariate polynomial, then
--   $$\operatorname{mult}_{t=0}P(a+tv)\ge\operatorname{mult}_a(P).$$
--
--   These two inequalities control loss of vanishing order under differentiation and line restriction over arbitrary characteristic.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: mult_a(P) - |e| with possibly infinite multiplicity → truncated subtraction in extended nonnegative naturals, with infinity minus any finite order equal to infinity; reason: when the finite right side is negative the source bound is automatic; all nonnegative and infinite cases agree
--   - encoding: a line L through a and the multiplicity of its nonzero univariate restriction at a → all nonzero directions v, lineMap a v P, and its natural rootMultiplicity at parameter zero cast to extended naturals; reason: the parametrization a + t v covers every line through a; a has parameter zero, and the nonzero restriction hypothesis excludes the zero-polynomial default
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Fact B.2, PDF page 22 / printed page 21.

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


/-- fact B 2; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem fact_B_2 {F : Type} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (e : Fin n →₀ ℕ) (a : Vec n F) :
    multiplicity P a - (KakeyaHasse.order e : ℕ∞) ≤ multiplicity (KakeyaHasse.hasse e P) a ∧
    (∀ (v : Vec n F), v ≠ 0 → KakeyaPolynomialMethods.lineMap a v P ≠ 0 →
      multiplicity P a ≤ ((KakeyaPolynomialMethods.lineMap a v P).rootMultiplicity 0 : ℕ∞)) := by sorry

end ParityDegreeDepth.Main
