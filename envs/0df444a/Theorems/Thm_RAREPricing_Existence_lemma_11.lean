-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_11
-- name    : RAREPricing.Existence.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:56.859484+00:00
-- url     : https://prove2.me/theorems/9047fa92-f454-46f1-814f-8b2215e0a729
-- title:
--   Lemma 11 — uniform utility improvement from adding η of one good
-- statement:
--   Let $v:[0,1]\times[0,1]^m\to\mathbb R$ be continuous with $v(\varepsilon,\cdot)$ strictly monotone on $[0,1]^m$ for every $\varepsilon\in[0,1]$. Fix a good $k$ and $\eta\in(0,1)$. Then there is $\delta>0$ such that for every $\varepsilon\in[0,1]$ and $z,y\in[0,1]^m$,
--   $$z_k\le1-\eta\ \text{ and }\ \|y-(z+\eta e_k)\|_\infty<\delta\ \Longrightarrow\ v(\varepsilon,y)>v(\varepsilon,z).$$
--   The same $\delta$ works for all $\varepsilon$, $z$, $y$.
--
--   It is the utility estimate behind the security parameters (Lemma 5) and the overpricing parameters (Lemma 6).
--
--   **Formalization Note.** $v$ is `ℝ → (Fin m → ℝ) → ℝ`, continuous on $[0,1]\times[0,1]^m$ as an uncurried function; $\|\cdot\|$ on `Fin m → ℝ` is Mathlib's sup norm; $e_k$ is `Pi.single k 1`.
--
--   Differences from the source:
--   - generalization: standing assumption $m\ge2$ → any $m$ (with a good $k$, so $m\ge1$); reason: the statement holds for every $m\ge1$ by the same compactness argument and specializes to $m\ge2$.
--   - encoding: $v$ defined on $[0,1]\times[0,1]^m$ → a function on $\mathbb R\times\mathbb R^m$ that is `ContinuousOn` the product set; reason: only values on that set enter the statement.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 29 (PDF 31), Lemma 11

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_11 {m : ℕ} (v : ℝ → (Fin m → ℝ) → ℝ)
    (hv_cont : ContinuousOn (Function.uncurry v) (Set.Icc (0 : ℝ) 1 ×ˢ cube m))
    (hv_mono : ∀ ε ∈ Set.Icc (0 : ℝ) 1, StrictMonoOn (v ε) (cube m))
    (k : Fin m) (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ > 0, ∀ ε ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ cube m, ∀ y ∈ cube m,
      z k ≤ 1 - η → ‖y - (z + η • (Pi.single k (1 : ℝ) : Fin m → ℝ))‖ < δ →
        v ε z < v ε y := by sorry

end RAREPricing.Existence
