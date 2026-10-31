-- Prove2me | Theorems.Thm_SlottingFees_corollary_1
-- name    : SlottingFees.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:41.870759+00:00
-- url     : https://prove2.me/theorems/577bb46f-a5e3-413b-a72f-6d2932e40c6f
-- title:
--   Corollary 1 — the retailer's stage-1 profit $\tilde\Pi_r(S)$ when $|A|=1$ and its monotonicity
-- statement:
--   Consider the low-variety subgame under the standing assumptions, with any optimal stage-3 pricing strategy and any stage-2 outcomes of (5)–(8) after each fee $S\ge0$. Let $v_i\ge v_j$ ($j\neq i$). The retailer's profit at fee $S$ is
--   $$
--   \tilde\Pi_r(S)=\begin{cases}\max\Bigl\{\dfrac{v_i}{16},\ \dfrac{(\sqrt{v_j}+\sqrt{v_j-8S})^2}{16}\Bigr\}+S-K & 0\le S\le v_j/8,\\[2mm] \dfrac{v_i}{16}+S-K & v_j/8<S\le v_i/8,\end{cases}\qquad(9)
--   $$
--   and $\tilde\Pi_r$ is non-increasing on the set of $S\le v_j/8$ with $\sqrt{v_i}\le\sqrt{v_j}+\sqrt{v_j-8S}$, and non-decreasing on the rest of $[0,v_i/8]$.
--
--   The monotonicity reduces the retailer's fee choice to the two candidates $S=0$ and $S=v_i/8$ (Proposition 1).
--
--   Differences from the source:
--   - encoding: dΠ̃_r(S)/dS ≤ 0 on the first set and ≥ 0 otherwise → AntitoneOn on the first set and MonotoneOn on the rest of [0, v_i/8]; reason: Π̃_r has a kink where the maximum in (9) switches, at which Lean's deriv is a junk 0; monotonicity on the sets gives the printed signs wherever the derivative exists
--   - reading: the |A| = 1 stage 2 of (5)-(8): the manufacturer that cannot enter offers its zero-profit price, the other solves (6)-(7) → IsStage2Outcome1: zero-profit price = least w ≥ c_l with non-negative profit; the entrant is the manufacturer whose zero-profit price gives the retailer the larger optimal gross profit, ties to manufacturer 1; (7) as the primitive condition that the retailer weakly prefers the entrant; reason: the paper does not say which manufacturer enters; this is its own logic (p.11) and makes the entrant the more attractive manufacturer of Lemma 2; (7) is equivalent to its closed form by Lemma 1
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Corollary 1, (9), p.12

import Mathlib
import Definitions.Def_SlottingFees_ClosedForms
import Definitions.Def_SlottingFees_Subgame1

namespace SlottingFees

/-- **Corollary 1**, p.12 (Alan, Kurtuluş, Nakkas, MSOM 2024, doi:10.1287/msom.2022.0143): the
retailer's stage-1 objective in the `|A| = 1` subgame.

Under the standing assumptions, for every optimal stage-3 pricing strategy and every choice of
stage-2 outcomes (5)–(8) after each fee `S ≥ 0`, and for `v_i ≥ v_j` (`j ≠ i`), the retailer's
profit `Π̃_r(S)` is

$$\tilde\Pi_r(S)=\begin{cases}\max\{v_i/16,\ (\sqrt{v_j}+\sqrt{v_j-8S})^2/16\}+S-K & 0\le S\le v_j/8,\\
v_i/16+S-K & v_j/8<S\le v_i/8,\end{cases}\qquad(9)$$

it is non-increasing on `{S ≤ v_j/8 : √v_i ≤ √v_j + √(v_j − 8S)}` and non-decreasing on the rest
of `[0, v_i/8]`.

**Formalization Note** The printed derivative signs `dΠ̃_r/dS ≤ 0` and `≥ 0` are stated as
`AntitoneOn` and `MonotoneOn` on the two sets: `Π̃_r` has a kink where the maximum in (9)
switches. Product 1 is `0`. -/
theorem corollary_1 (ω : Params) (hω : ω.Standing) (σ : Fin 2 → ℝ → ℝ)
    (hσ : IsOptPricing1 ω σ) (o : ℝ → Option (Fin 2 × ℝ))
    (ho : ∀ S, 0 ≤ S → IsStage2Outcome1 ω σ S (o S)) (i : Fin 2)
    (hv : ω.v (other i) ≤ ω.v i) :
    (∀ S, 0 ≤ S → S ≤ ω.v (other i) / 8 →
      payoff1 ω σ S (o S) =
        max (ω.v i / 16)
          ((Real.sqrt (ω.v (other i)) + Real.sqrt (ω.v (other i) - 8 * S)) ^ 2 / 16)
          + S - ω.K) ∧
    (∀ S, ω.v (other i) / 8 < S → S ≤ ω.v i / 8 →
      payoff1 ω σ S (o S) = ω.v i / 16 + S - ω.K) ∧
    AntitoneOn (fun S => payoff1 ω σ S (o S))
      {S | 0 ≤ S ∧ S ≤ ω.v (other i) / 8 ∧
        Real.sqrt (ω.v i) ≤ Real.sqrt (ω.v (other i)) + Real.sqrt (ω.v (other i) - 8 * S)} ∧
    MonotoneOn (fun S => payoff1 ω σ S (o S))
      {S | 0 ≤ S ∧ S ≤ ω.v i / 8 ∧
        ¬ (S ≤ ω.v (other i) / 8 ∧
          Real.sqrt (ω.v i) ≤ Real.sqrt (ω.v (other i)) + Real.sqrt (ω.v (other i) - 8 * S))} := by sorry

end SlottingFees
