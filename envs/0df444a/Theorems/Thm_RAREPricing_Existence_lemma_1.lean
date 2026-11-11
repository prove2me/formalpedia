-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_1
-- name    : RAREPricing.Existence.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:45.883189+00:00
-- url     : https://prove2.me/theorems/a2b75ade-301d-45fc-87af-c0139237c2bc
-- title:
--   Lemma 1 — KKM lemma for closed sets on a scaled simplex with the support covering condition
-- statement:
--   Let $m\ge1$, $\beta>0$, and let $C_1,\dots,C_m$ be closed subsets of the scaled simplex $\beta\Delta_m=\{x\in\mathbb R^m_{\ge0}:\sum_jx_j=\beta\}$. Suppose every $x\in\beta\Delta_m$ lies in $C_j$ for some $j$ in its support $\{j: x_j>0\}$. Then
--   $$\bigcap_{j=1}^m C_j\neq\emptyset ,$$
--   i.e. some point of $\beta\Delta_m$ lies in every $C_j$.
--
--   This is the Knaster–Kuratowski–Mazurkiewicz lemma in the closed-set form the paper uses twice: in Lemma 2 (on a standard simplex) and in Lemma 4 (on $\beta\Delta_m$).
--
--   **Formalization Note.** Points are `Fin m → ℝ`; "closed subset of $\beta\Delta_m$" is `IsClosed` in $\mathbb R^m$ together with `C j ⊆ scaledSimplex m β` (equivalent, since $\beta\Delta_m$ is closed).
--
--   Differences from the source:
--   - encoding: closed subsets of $\beta\Delta_m$ (relative topology) → `IsClosed (C j)` in `Fin m → ℝ` with `C j ⊆ scaledSimplex m β`; reason: $\beta\Delta_m$ is closed in $\mathbb R^m$, so the two notions coincide.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 14 (PDF 16), Lemma 1

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_1 (m : ℕ) (hm : 1 ≤ m) (β : ℝ) (hβ : 0 < β) (C : Fin m → Set (Fin m → ℝ))
    (hC_sub : ∀ j, C j ⊆ scaledSimplex m β) (hC_closed : ∀ j, IsClosed (C j))
    (hcover : ∀ x ∈ scaledSimplex m β, ∃ j, 0 < x j ∧ x ∈ C j) :
    ∃ x ∈ scaledSimplex m β, ∀ j, x ∈ C j := by sorry

end RAREPricing.Existence
