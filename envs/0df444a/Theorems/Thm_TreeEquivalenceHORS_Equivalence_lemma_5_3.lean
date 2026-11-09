-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_3
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:08.888341+00:00
-- url     : https://prove2.me/theorems/3ada0052-29cc-4c2f-a2b7-e4ee58727bab
-- title:
--   Lemma 5.3 (Church arithmetic): realizability of Zero, One, Succ, Add, Mul, Pos, Neg and of the observation $t\,a\,z\Vdash_o a^nz$
-- statement:
--   Fix a compiled scheme $G=G^\diamond_M$ and write $\mathrm{Num}(t,n)$ for $t\Vdash_N(f,X)\mapsto f^n(X)$ (Equation (18)), for closed $t:N$.
--
--   1. $\mathrm{Num}(\mathrm{Zero},0)$ and $\mathrm{Num}(\mathrm{One},1)$.
--   2. If $\mathrm{Num}(t,m)$ and $\mathrm{Num}(u,n)$, then $\mathrm{Num}(\mathrm{Succ}\,t,m+1)$, $\mathrm{Num}(\mathrm{Add}\,t\,u,m+n)$ and $\mathrm{Num}(\mathrm{Mul}\,t\,u,mn)$.
--   3. For closed $t_1,\dots,t_4:N$ and $\alpha,\beta,\gamma,\delta\in\mathbb N$ with $\mathrm{Num}(t_1,\alpha)$, $\mathrm{Num}(t_2,\beta)$, $\mathrm{Num}(t_3,\gamma)$, $\mathrm{Num}(t_4,\delta)$:
--   $$\mathrm{Num}(\mathrm{Pos}\,t_1t_2t_3t_4,\alpha\gamma+\beta\delta),\qquad\mathrm{Num}(\mathrm{Neg}\,t_1t_2t_3t_4,\alpha\delta+\beta\gamma),$$
--   the two coordinates of the signed-pair product $(\alpha,\beta)\otimes(\gamma,\delta)$.
--   4. $\mathrm{Num}(t,n)$ implies $t\,a\,z\Vdash_o a^nz$, the observation map of the chain of $n$ nodes $a$ ending in $z$.
--
--   The relation quantifies over all related functional arguments, which is what makes $\mathrm{Mul}$ correct.
--
--   Differences from the source:
--   - encoding: Num(t, n) and Pol_m(p, q) are defined for closed terms t : N and p, q : P → `Num` and `Pol` include the conjuncts `typeOf [] t = some N` (resp. `P`); reason: the source defines the relations only on closed typed terms; the conjunct records that domain
--   - encoding: V_o = partial maps ℕ* ⇀ Σ₀ with † for undefined → `Val .o = List ℕ → Option (Fin 3)`, `none` = †, `Fin 3` indexing z, a, b; reason: same set of partial maps
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.3, printed p. 17 / PDF p. 19

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.3 (Church arithmetic)** (printed p. 17 / PDF p. 19), in every compiled scheme `G`:
`Num(Zero, 0)`, `Num(One, 1)`; if `Num(t, m)` and `Num(u, n)` then `Num(Succ t, m + 1)`,
`Num(Add t u, m + n)`, `Num(Mul t u, mn)`; if `Num(t₁, α)`, `Num(t₂, β)`, `Num(t₃, γ)`, `Num(t₄, δ)` then
`Num(Pos t₁ t₂ t₃ t₄, αγ + βδ)` and `Num(Neg t₁ t₂ t₃ t₄, αδ + βγ)` (the coordinates of
`(α, β) ⊗ (γ, δ)`); and `Num(t, n)` implies `t a z ⊩_o aⁿ z`. -/
theorem lemma_5_3 (side : Side) (M : Machine) :
    let G := compile side M
    Num G (.nt iZero) 0 ∧ Num G (.nt iOne) 1 ∧
    (∀ (t u : Tm) (m n : ℕ), Num G t m → Num G u n →
      Num G (.app (.nt iSucc) t) (m + 1) ∧ Num G (Tm.apps (.nt iAdd) [t, u]) (m + n) ∧
        Num G (Tm.apps (.nt iMul) [t, u]) (m * n)) ∧
    (∀ (t₁ t₂ t₃ t₄ : Tm) (α β γ δ : ℕ),
      Num G t₁ α → Num G t₂ β → Num G t₃ γ → Num G t₄ δ →
        Num G (Tm.apps (.nt iPos) [t₁, t₂, t₃, t₄]) (α * γ + β * δ) ∧
          Num G (Tm.apps (.nt iNeg) [t₁, t₂, t₃, t₄]) (α * δ + β * γ)) ∧
    (∀ (t : Tm) (n : ℕ), Num G t n → Real G .o (Tm.apps t [ta, tz]) (chainVal n)) := by sorry

end TreeEquivalenceHORS.Equivalence
