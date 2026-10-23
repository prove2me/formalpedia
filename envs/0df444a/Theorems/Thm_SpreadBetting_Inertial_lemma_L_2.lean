-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_L_2
-- name    : SpreadBetting.Inertial.lemma_L_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:25.448382+00:00
-- url     : https://prove2.me/theorems/b21395dd-f965-460a-9196-af2774129413
-- title:
--   Lemma L.2, p. 70 — for strictly upper bounded ρ and a Z̄-threshold strategy, Σ_t Ẽ^z_1 I{Z_t ≤ M} = Ẽ^z_1 ũ(Z_{T+1}) − ũ(z) with ũ increasing, closed form (L.2)–(L.3)
-- statement:
--   Let the market satisfy the standing assumptions and let $\rho : \mathbb Z_+ \to (0, \tfrac12 - \alpha)$ be **strictly upper bounded** (Definition 5): $\sup_{z \in \mathbb Z_+}\rho(z) < \tfrac12 - \alpha$; extend it to $\mathbb Z$ by (E.1). Under $H_1$ let the informed bettor use the $\bar Z$-threshold strategy and write $\tilde{\mathbb E}_1^z$ for expectations from $Z_1 = z$.
--
--   1. For $\bar Z \in \mathbb Z$ and $M \in \mathbb Z$ with $M > \bar Z - 2$, define $q(m) = \frac{1/2 - \rho(m)}{1/2 + \rho(m)}$,
--   $$
--   \tilde\beta = -\prod_{m=\bar Z}^M q(m) - \sum_{k=\bar Z}^M \frac{1}{\tfrac12 - \rho(k)}\prod_{m=k}^M q(m),\qquad \beta = -q(M+1)\,\tilde\beta, \tag{L.3}
--   $$
--   and $\tilde u$ by (L.2): for $\bar Z - 2 < z \le M$,
--   $$
--   \tilde u(z) = \Big(1 + \sum_{n=z+1}^M \prod_{m=n}^M \frac{1}{q(m)}\Big)\tilde\beta + \sum_{n=z+1}^M\sum_{k=n}^M \frac{1}{\tfrac12 + \rho(k)}\prod_{m=n}^k \frac{1}{q(m)},
--   $$
--   $\tilde u(M+1) = 0$, and $\tilde u(z) = \big(1 + \sum_{n=M+2}^{z-1}\prod_{m=M+2}^n q(m)\big)\beta$ for $z \ge M+2$. Then $\tilde\beta < 0 < \beta$, $\tilde u$ is strictly increasing on $\{z > \bar Z - 2\}$, and for all $z > \bar Z - 2$ and $T \in \mathbb Z_+$,
--   $$
--   \sum_{t=1}^T \tilde{\mathbb E}_1^z\, \mathbb I\{Z_t \le M\} = \tilde{\mathbb E}_1^z\, \tilde u(Z_{T+1}) - \tilde u(z). \tag{L.1}
--   $$
--   2. For $\bar Z = -\infty$ (the informed bettor never bets) and every $M \in \mathbb Z$ there is a strictly increasing $\tilde u : \mathbb Z \to \mathbb R$ satisfying (L.1) for all $z \in \mathbb Z$ and $T \in \mathbb Z_+$.
--
--   The lemma evaluates the expected time the market state spends below level $M$, the key quantity for transience.
--
--   **Formalization Note** "Increasing" is read as strictly increasing, as in Step 2 of the paper's proof (p. 74). The closed form is stated for finite $\bar Z$, where its sums are finite; for $\bar Z = -\infty$ the existence part of the lemma is stated. Definition 5 is encoded as $\rho(z) \le \tfrac12 - \alpha - \delta$ for some $\delta > 0$. $\tilde u$ is a function on $\mathbb Z$ whose values below $\bar Z - 1$ are irrelevant (the chain never visits them).
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 70, Lemma L.2, Definition 5, (L.1)–(L.3); Definition 4 p. 68

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_L_2 (M : Market) (hM : M.Standing) (ρp : ℕ → ℝ)
    (hρ : ∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M))
    (hbdd : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ, 1 ≤ z → ρp z ≤ 1 / 2 - alpha M - δ) :
    -- Z̄ ∈ ℤ: the closed form (L.2)–(L.3)
    (∀ Zb Mx : ℤ, Zb - 2 < Mx →
      let ρ := rhoExt M ρp
      let q : ℤ → ℝ := fun m => (1 / 2 - ρ m) / (1 / 2 + ρ m)
      let βt : ℝ := -(∏ m ∈ Finset.Icc Zb Mx, q m)
        - ∑ k ∈ Finset.Icc Zb Mx, (1 / (1 / 2 - ρ k)) * ∏ m ∈ Finset.Icc k Mx, q m
      let β : ℝ := -q (Mx + 1) * βt
      let ut : ℤ → ℝ := fun z =>
        if z ≤ Mx then
          (1 + ∑ n ∈ Finset.Icc (z + 1) Mx,
              ∏ m ∈ Finset.Icc n Mx, (1 / 2 + ρ m) / (1 / 2 - ρ m)) * βt
            + ∑ n ∈ Finset.Icc (z + 1) Mx, ∑ k ∈ Finset.Icc n Mx,
                (1 / (1 / 2 + ρ k)) * ∏ m ∈ Finset.Icc n k, (1 / 2 + ρ m) / (1 / 2 - ρ m)
        else if z = Mx + 1 then 0
        else (1 + ∑ n ∈ Finset.Icc (Mx + 2) (z - 1), ∏ m ∈ Finset.Icc (Mx + 2) n, q m) * β
      let ξ := threshStrat 1 (fun z => z < Zb)
      βt < 0 ∧ 0 < β ∧ StrictMonoOn ut {z : ℤ | Zb - 2 < z} ∧
      ∀ z : ℤ, Zb - 2 < z → ∀ T : ℕ, 1 ≤ T →
        cumExp M ρp 1 ξ (fun z _ _ => indic (z ≤ Mx)) T [] z
          = termExp M ρp 1 ξ ut T [] z - ut z) ∧
    -- Z̄ = -∞
    (∀ Mx : ℤ, ∃ ut : ℤ → ℝ, StrictMono ut ∧
      ∀ z : ℤ, ∀ T : ℕ, 1 ≤ T →
        cumExp M ρp 1 (threshStrat 1 (fun _ => False)) (fun z _ _ => indic (z ≤ Mx)) T [] z
          = termExp M ρp 1 (threshStrat 1 (fun _ => False)) ut T [] z - ut z) := by sorry

end SpreadBetting.Inertial
