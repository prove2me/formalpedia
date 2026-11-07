-- Prove2me | Theorems.Thm_PRUPermLayer_fact_2_4
-- name    : PRUPermLayer.fact_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:56.167418+00:00
-- url     : https://prove2.me/theorems/0cd9726c-0654-433c-9be0-dfc64f8a0515
-- title:
--   Fact 2.4 — $|\mathrm{Tr}(\Pi_A\Pi_B\rho\Pi_B\Pi_A) - \mathrm{Tr}(\Pi_{A\cap B}\rho)| \le c(A,B)^2$
-- statement:
--   For subspaces $A, B$ of a finite-dimensional Hilbert space and every density operator $\rho$,
--   $$
--   \big|\mathrm{Tr}(\Pi_A\Pi_B\,\rho\,\Pi_B\Pi_A) - \mathrm{Tr}(\Pi_{A\cap B}\,\rho)\big| \le c(A,B)^2 .
--   $$
--
--   The paper imports this from [FLM+26, Corollary 7.13]. It compares projecting onto the intersection with projecting onto the two subspaces in turn.
--
--   Differences from the source:
--   - encoding: subspaces of the paper's finite-dimensional spaces → subspaces of $\mathbb C^\iota$ for any finite index type $\iota$; reason: every finite-dimensional Hilbert space is some $\mathbb C^\iota$
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.4, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PRUPermLayer_friedrichsCos
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Fact 2.4** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.4, p.10 (PDF p.12), quoting [FLM+26, Corollary 7.13]). For
subspaces `A, B` and every density operator `ρ`,
`|Tr(Π_A Π_B ρ Π_B Π_A) − Tr(Π_{A∩B} ρ)| ≤ c(A, B)²`.

**Formalization Note** Any finite index type `ι`; `|·|` is the modulus of the complex difference
of the two traces. -/
theorem fact_2_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Submodule ℂ (EuclideanSpace ℂ ι))
    (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ‖(projMat A * projMat B * ρ * projMat B * projMat A).trace - (projMat (A ⊓ B) * ρ).trace‖ ≤
      friedrichsCos A B ^ 2 := by sorry

end PRUPermLayer
