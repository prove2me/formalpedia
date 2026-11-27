-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_22
-- name    : SurrogateOps.Supplement.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:40:29.091803+00:00
-- url     : https://prove2.me/theorems/78266147-ecdb-4182-8da0-d1a800736e3d
-- title:
--   Theorem 22, p.13 (corrected: $\bar\Delta$ chosen as in Lemma 21) — function accuracy of a quotient of two models at/near $x_0$, with the explicit min-constant
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be continuous, $F=f_1/f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}/\tilde f_{2,\Delta}$, with $f_2(x)\neq0$ and $\tilde f_{2,\Delta}(x)\neq0$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$. Let $M_{1/f_2}(x_0)$ and $M_{f_1}(x_0)$ bound $|1/f_2|$ and $|f_1|$ on $B_{\bar\Delta}(x_0)$. Suppose that for $i=1,2$ the class $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy of $f_i$ at (resp. near) $x_0$ with constant $\kappa^f_i(x_0)$, that $M_{\tilde f_1}(x_0)$ bounds $|\tilde f_{1,\Delta}|$ uniformly at (resp. near) $x_0$, and that $N^f_2>0$. Let $N^f_F=\min\{N^f_1,N^f_2\}$. Then:
--
--   1. some $\Delta_0\in(0,\bar\Delta]$ satisfies $\Delta_0^{N^f_2}M_{1/f_2}(x_0)\kappa^f_2(x_0)<1$;
--   2. for every such $\Delta_0$, with $\tilde M_{1/\tilde f_2}(x_0)=M_{1/f_2}(x_0)/(1-\Delta_0^{N^f_2}M_{1/f_2}(x_0)\kappa^f_2(x_0))$ and
--   $$
--   \begin{aligned}
--   K^f_F(x_0)=\min\Bigl\{&M_{1/f_2}\kappa^f_1\Delta_0^{N^f_1-N^f_F}+M_{1/f_2}\tilde M_{1/\tilde f_2}M_{\tilde f_1}\kappa^f_2\Delta_0^{N^f_2-N^f_F},\\
--   &\tilde M_{1/\tilde f_2}\kappa^f_1\Delta_0^{N^f_1-N^f_F}+M_{1/f_2}\tilde M_{1/\tilde f_2}M_{f_1}\kappa^f_2\Delta_0^{N^f_2-N^f_F}\Bigr\}
--   \end{aligned}
--   $$
--   (all quantities at $x_0$), for every $\Delta\in(0,\Delta_0]$: (i) in the "at" case $|F(x_0)-\tilde F_\Delta(x_0)|\le K^f_F(x_0)\Delta^{N^f_F}$; (ii) in the "near" case $|F(x)-\tilde F_\Delta(x)|\le K^f_F(x_0)\Delta^{N^f_F}$ for all $x\in B_\Delta(x_0)$. In particular $\{\tilde F_\Delta\}_{(0,\Delta_0]}$ provides order-$N^f_F$ function accuracy of $F$ at (resp. near) $x_0$.
--
--   The quotient behaves at least as well as its worse factor once the denominator models are kept away from zero.
--
--   **Formalization Note** The paper's $\bar\Delta$ in this theorem is the "sufficiently small $\bar\Delta$" of Lemma 21, which Lean calls $\Delta_0$; on an arbitrary interval $(0,\bar\Delta]$ the bound is false.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: standing assumption of §4 (p.12): f₂(x) ≠ 0 and f̃_{2,Δ}(x) ≠ 0 for all Δ ∈ (0, Δ̄] and x ∈ B_Δ(x₀) → the hypothesis hne; reason: copied from the section's standing assumption; it is needed in Lean, where x / 0 = 0
--   - encoding: M_{1/f₂}(x₀), the bound of |1/f₂| on B_Δ̄(x₀) (p.12) → a number M with |1 / f₂ x| ≤ M for all x ∈ closedBall x0 Δbar; reason: the page names the bound without fixing it; a continuous f₂ without zeros on the compact ball always has one
--   - encoding: M-bounds M_{f₁}(x₀), M_{f̃₁}(x₀) → numbers with bounding hypotheses on |f₁| over B_Δ̄(x₀) and on |f̃_{1,Δ}| at x₀ (case i) or on B_Δ(x₀) (case ii) for Δ ∈ (0, Δ̄]; reason: the page says "we use … to denote these bounds" (p.4); the theorem holds for every valid choice, and no sSup junk value can enter
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - correction: the conclusion on the given (0, Δ̄], whose Δ̄ is only implicitly the "sufficiently small Δ̄" of Lemma 21 → (a) some Δ₀ ∈ (0, Δ̄] has Δ₀^{N^f_2} M_{1/f₂}(x₀) κ^f_2(x₀) < 1, and (b) for every such Δ₀ the conclusion holds for the class on (0, Δ₀], with Δ₀ in place of Δ̄; reason: counterexample on the given interval: d = 1, x₀ = 0, Δ̄ = 1, f₂ = 1, f̃_{2,Δ} ≡ c(Δ) with c = 1 for Δ < 1/4 and at Δ = 1/2, c = |Δ − 1/2| otherwise (order-1 function accuracy with κ = 4, exact derivatives, c never 0), f̃₁ = f₁ ∈ {1, x, x²}: the function, gradient, Hessian error of the quotient is a multiple of |1 − 1/c(Δ)|, unbounded as Δ → 1/2; the inequality is the one the proof of Lemma 21 imposes (p.13), and (a) keeps every instance of the source
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 22, p.13; Lemma 21, p.13; standing assumptions of §4, p.12

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 22 (Function accuracy at/near `x0`), for `Δ̄` chosen as in Lemma 21.** Chen, Hare,
Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models,
arXiv:2112.08411v1, Theorem 22, p.13 (with Lemma 21, p.13, and the standing assumptions of §4, p.12).
For `F = f₁/f₂`, `F̃_Δ = f̃_{1,Δ}/f̃_{2,Δ}`, `N^f_F = min{N^f_1, N^f_2}` and `N^f_2 > 0`: (a) some
`Δ₀ ∈ (0, Δ̄]` satisfies `Δ₀^{N^f_2} M_{1/f₂} κ^f_2 < 1`; (b) for every such `Δ₀`, with
`M̃ = M_{1/f₂}/(1 - Δ₀^{N^f_2} M_{1/f₂} κ^f_2)` and `K` the page's minimum with `Δ₀` for `Δ̄`, in case (i)
`|F(x0) - F̃_Δ(x0)| ≤ K Δ^{N^f_F}`, in case (ii) the same for every `x ∈ B_Δ(x0)`, for all
`Δ ∈ (0, Δ₀]`, and `{F̃_Δ}_{(0,Δ₀]}` provides order-`N^f_F` function accuracy of `F` at/near `x0`.

**Formalization Note.** The page's `Δ̄` is the "sufficiently small `Δ̄`" of Lemma 21: Lean names it
`Δ₀` and states the choice as (a); without it the bound is false (`MODERATION_NOTES.md`). `hne` is the
standing assumption of §4. `M` is `M_{1/f₂}(x0)` (bound of `|1/f₂|` on `B_Δ̄(x0)`), `Mf₁` is `M_{f₁}(x0)`
(bound of `|f₁|` on `B_Δ̄(x0)`), `Mft₁` is `M_{f̃₁}(x0)` (uniform bound of the models, at `x0` in case
(i), near `x0` in case (ii)); they are hypotheses rather than `sSup`s. -/
theorem theorem_22 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₁ N₂ κ₁ κ₂ M Mf₁ Mft₁ NF : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hne : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, f₂ x ≠ 0 ∧ fm₂ Δ x ≠ 0)
    (hM : ∀ x ∈ Metric.closedBall x0 Δbar, |1 / f₂ x| ≤ M)
    (hMf₁ : ∀ x ∈ Metric.closedBall x0 Δbar, |f₁ x| ≤ Mf₁)
    (hNF : NF = min N₁ N₂) (hN₂ : 0 < N₂) :
    (∃ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ N₂ * M * κ₂ < 1) ∧
    (FunAccAt f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccAt f₂ fm₂ x0 Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, |fm₁ Δ x0| ≤ Mft₁) →
      ∀ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ N₂ * M * κ₂ < 1 →
        (∀ Δ ∈ Set.Ioc 0 Δ₀,
          |f₁ x0 / f₂ x0 - fm₁ Δ x0 / fm₂ Δ x0| ≤
            min (M * κ₁ * Δ₀ ^ (N₁ - NF)
                  + M * (M / (1 - Δ₀ ^ N₂ * M * κ₂)) * Mft₁ * κ₂ * Δ₀ ^ (N₂ - NF))
                ((M / (1 - Δ₀ ^ N₂ * M * κ₂)) * κ₁ * Δ₀ ^ (N₁ - NF)
                  + M * (M / (1 - Δ₀ ^ N₂ * M * κ₂)) * Mf₁ * κ₂ * Δ₀ ^ (N₂ - NF))
              * Δ ^ NF) ∧
        ∃ κ, FunAccAt (fun x => f₁ x / f₂ x) (fun Δ x => fm₁ Δ x / fm₂ Δ x) x0 Δ₀ NF κ) ∧
    (FunAccNear f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccNear f₂ fm₂ x0 Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm₁ Δ x| ≤ Mft₁) →
      ∀ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ N₂ * M * κ₂ < 1 →
        (∀ Δ ∈ Set.Ioc 0 Δ₀, ∀ x ∈ Metric.closedBall x0 Δ,
          |f₁ x / f₂ x - fm₁ Δ x / fm₂ Δ x| ≤
            min (M * κ₁ * Δ₀ ^ (N₁ - NF)
                  + M * (M / (1 - Δ₀ ^ N₂ * M * κ₂)) * Mft₁ * κ₂ * Δ₀ ^ (N₂ - NF))
                ((M / (1 - Δ₀ ^ N₂ * M * κ₂)) * κ₁ * Δ₀ ^ (N₁ - NF)
                  + M * (M / (1 - Δ₀ ^ N₂ * M * κ₂)) * Mf₁ * κ₂ * Δ₀ ^ (N₂ - NF))
              * Δ ^ NF) ∧
        ∃ κ, FunAccNear (fun x => f₁ x / f₂ x) (fun Δ x => fm₁ Δ x / fm₂ Δ x) x0 Δ₀ NF κ) := by sorry

end SurrogateOps.Supplement
