-- Prove2me | Theorems.Thm_SensLabelCover_DH_proposition_8_1
-- name    : SensLabelCover.DH.proposition_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:21.637724+00:00
-- url     : https://prove2.me/theorems/2f66eca1-9ce9-4a9c-9583-dc57d1f8cf23
-- title:
--   Proposition 8.1 — Arora–Sudan low-degree test: a list of at most $4/\kappa$ degree-$D$ polynomials, depending only on $f$, explains all line–point agreement up to $2\kappa$
-- statement:
--   There are absolute constants $C_0,C_1>0$ such that the following holds for every finite field $F$ with $q=|F|$, all integers $m\ge1$, $D\ge0$ and every $0<\kappa\le1/2$ with $q\ge C_0((D+1)/\kappa)^{C_1}$. Every $f:F^m\to F$ has a list $L_f$ of at most $4/\kappa$ polynomials in $F[x_1,\dots,x_m]$ of total degree at most $D$ such that, for every assignment $\ell\mapsto B_\ell$ of polynomial functions of degree at most $D$ to the affine lines $\ell\subseteq F^m$,
--   $$\Pr_{\ell,\,z\in\ell}\big[B_\ell(z)=f(z)\ \wedge\ B_\ell\notin\{P|_\ell:P\in L_f\}\big]\le2\kappa,$$
--   with $\ell$ a uniform line and $z$ a uniform point on it. The list depends only on $f$, not on the line assignment.
--
--   This list form of the low-degree test, a cited result ([2] in the paper), is what the paper's stage-zero construction uses to decode line labels into a few global polynomials.
--
--   Differences from the source:
--   - encoding: $m$ implicit → $m\ge1$; reason: $F^0$ has no lines, so the probability is undefined there.
--   - encoding: lines, uniform line and point, and line assignments → lines as finite point sets $\{a+tv\}$ with $v\neq0$, averages over the finite set of lines and their points, $B:\text{lines}\to(F^m\to F)$ read on its line, degree $\le D$ in some affine parametrization; reason: same objects (the paper notes the parametrization does not matter).
--   - encoding: the list $L_f$ → a finite set of polynomials with $|L_f|\le4/\kappa$; reason: duplicates do not change the event.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 42 (PDF 45), Proposition 8.1

import Mathlib
import Definitions.Def_SensLabelCover_DH_LowDegreeTest

namespace SensLabelCover.DH

/-- Proposition 8.1 (Arora–Sudan low-degree test, list form), p. 42 (PDF p. 45). The constants
`C₀, C₁` are absolute: they precede the field, `m`, `D` and `κ`. -/
theorem proposition_8_1 :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (m D : ℕ) (κ : ℝ),
        1 ≤ m → 0 < κ → κ ≤ 1 / 2 →
        C₀ * (((D : ℝ) + 1) / κ) ^ C₁ ≤ (Fintype.card F : ℝ) →
        ∀ f : (Fin m → F) → F, ∃ L : Finset (MvPolynomial (Fin m) F),
          (∀ P ∈ L, P.totalDegree ≤ D) ∧ (L.card : ℝ) ≤ 4 / κ ∧
          ∀ B : Finset (Fin m → F) → (Fin m → F) → F,
            (∀ ℓ ∈ lines F m, IsLinePoly D ℓ (B ℓ)) →
            lineTestFailProb f B L ≤ 2 * κ := by sorry

end SensLabelCover.DH
