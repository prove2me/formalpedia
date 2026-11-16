-- Prove2me | Theorems.Thm_PolyEulerFlow_Supplement_theorem_11
-- name    : PolyEulerFlow.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:09:40.443349+00:00
-- url     : https://prove2.me/theorems/2b4ac461-b45e-4648-9a6e-d7c73cdfbf15
-- title:
--   Theorem 11 — the polynomial-time field decides in continuous time with polynomial arc length
-- statement:
--   Let $L\subseteq\mathbb N^d$ be in $\mathsf P$. There is a scale-controlled rational polynomial system witnessing Theorem 8, item 3 (mesh-uniform decision with threshold $S$, horizon $Q$, box $[lo,hi]$ and output coordinate $o$, and active length at most $\Lambda(s)$ up to $\lceil Q(s)/\eta\rceil$), and there are polynomials $Q'$ and $\Lambda'$, such that for every input $x$ and every scale $s\ge S(\ell(x))$, $h=2^{-s}$:
--
--   1. a solution of $\dot z=F(x,h,z)$, $z(0)=c(x,h)$, on $[0,\infty)$ exists;
--   2. every such solution stays in $[lo,hi]$ for $t\ge0$ and satisfies $|z(t)(o)-1_L(x)|\le1/4$ for all $t\ge Q'(s)$;
--   3. its active arc length up to the decision is polynomial in $s$:
--   $$\int_0^{Q'(s)}\|F(x,h,z(t))\|_\infty\,dt\le\Lambda'(s).$$
--
--   The same field thus decides the same language in discrete and continuous time, with polynomial physical time and length.
--
--   **Formalization Note** Solutions are the published `IsForcedSolution` with zero forcing (a continuous solution of the integral equation on $[0,\infty)$).
--
--   Differences from the source:
--   - reading: let F be the field constructed for Theorem 8 → for every L ∈ P there is a witness of Theorem 8 item 3, with its active-length bound, whose flow has the stated properties; reason: the construction is not a named object; Theorem 11 is a property of a Theorem 8 witness
--   - reading: the solution of ż = F(x, h, z) → a solution on [0, ∞) of the integral equation exists, and every such solution has the properties; reason: uniqueness is not needed; asserting existence and all solutions is the strongest reading
--   - reading: decides the same language after polynomial physical time → stays in the box for t ≥ 0 and |z(t)(o) − 1_L(x)| ≤ 1/4 for t ≥ Q′(s), Q′ a polynomial; reason: Definition 4's decision (box and output) in continuous time
--   - encoding: active arc length up to the decision → ∫_0^{Q′(s)} ‖F(x, h, z(t))‖∞ dt ≤ Λ′(s), Λ′ a polynomial with natural coefficients; reason: Definition 7's length of a flow; polynomials with natural coefficients dominate integer ones
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 11, p.8 (PDF 10); proof p.38 (PDF 40); Definition 7, p.6

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_ScaleSystem
import Definitions.Def_PolyEulerFlow_IsForcedSolution

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- **Theorem 11 (Same field in continuous time)**, p.8 (PDF 10). Bournez, One Polynomial Field for Every Euler Step and the Flow
(manuscript, sha256 c4e01b2b…): "Let F be the field constructed for Theorem 8. For every fixed input and permitted scale, the solution of
ż = F(x, h, z) decides the same language after polynomial physical time. The active arc length up to the decision is polynomial in s."

For every `L ∈ P` there is a witness of Theorem 8, Item 3 (with its polynomial active length), and polynomials `Q′`, `Λ′`, such that for every
input `x` and every `s ≥ S(ℓ(x))`, `h = 2^{-s}`: a solution of `ż = F(x, h, z)`, `z(0) = c(x, h)` on `[0, ∞)` exists, and every such solution
stays in the box, has `|o(t) − 1_L(x)| ≤ 1/4` for all `t ≥ Q′(s)`, and has arc length `∫_0^{Q′(s)} ‖F(x, h, z(t))‖∞ dt ≤ Λ′(s)`.

**Formalization Note.** "The field constructed for Theorem 8" is read as an existential witness of Theorem 8's Item 3 with its length bound;
the solution is the published `IsForcedSolution` with zero forcing; existence of the solution is asserted. -/
theorem theorem_11 {d : ℕ} (L : Set (Fin d → ℕ)) (hL : InP L) :
    ∃ (m : ℕ) (S : ScaleSystem d m) (Sthr Q Λ Q' Λ' : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ),
      (∀ η : ℝ, 0 < η → η ≤ 1 → S.StablyDecidesAt L Sthr Q o lo hi η) ∧
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (x : Fin d → ℕ) (s : ℕ), Sthr.eval (vecLength x) ≤ s →
          activeLengthOn (S.orbit x s η (fun _ => 0)) 0 ⌈((Q.eval s : ℕ) : ℝ) / η⌉₊ ≤ ((Λ.eval s : ℕ) : ℝ)) ∧
      ∀ (x : Fin d → ℕ) (s : ℕ), Sthr.eval (vecLength x) ≤ s →
        (∃ z : ℝ → Fin m → ℝ, IsForcedSolution (S.field x (scale s)) (S.init x (scale s)) (fun _ => 0) z) ∧
        ∀ z : ℝ → Fin m → ℝ, IsForcedSolution (S.field x (scale s)) (S.init x (scale s)) (fun _ => 0) z →
          (∀ t : ℝ, 0 ≤ t → z t ∈ Set.Icc lo hi) ∧
          (∀ t : ℝ, ((Q'.eval s : ℕ) : ℝ) ≤ t → |z t o - langIndicator L x| ≤ 1 / 4) ∧
          ∫ u in (0 : ℝ)..((Q'.eval s : ℕ) : ℝ), ‖S.field x (scale s) (z u)‖ ≤ ((Λ'.eval s : ℕ) : ℝ) := by sorry

end PolyEulerFlow.Supplement
