-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_22
-- name    : TwoOptAllExp.TSP.Supplement.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:49:46.322742+00:00
-- url     : https://prove2.me/theorems/c50daf12-d6c3-468c-a936-27d9910372b9
-- title:
--   Lemma 22 — $\Omega_m$ and $\bar\Omega_m$ have equal flip parities and swap the phase
-- statement:
--   In the instance $I_n$ ($n\ge1$) of Section 5, for every $0\le m\le n$:
--
--   1. $\Omega_m$ and $\bar\Omega_m$ have the same flip parity on every variable (each variable occurs in both an even or in both an odd number of times);
--   2. if $F_0,\dots,F_m$ are in phase $\varepsilon\in\{0,1\}$ under $\sigma$, then applying either complete string $\Omega_m$ or $\bar\Omega_m$ to $\sigma$ (flipping its entries successively) leaves $F_0,\dots,F_m$ in phase $1-\varepsilon$.
--
--   Differences from the source:
--   - encoding: "for every 0 ≤ m ≤ n" in the instance I_n of Section 5 → hypotheses 1 ≤ n and m ≤ n, assignments of I_n; reason: Section 5's I_n is defined for n ≥ 1
--   - encoding: applying a string → foldl of flipX over the string; reason: flips its entries successively
--   - encoding: same flip parity on every variable → equal counts modulo 2 for every name x : Vx; reason: Vx is a type of vertex names; names outside F_0 through F_m occur zero times in both strings, so this adds no condition on an instance
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 22, p. 31

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Lemma 22** (p. 31). For every `0 ≤ m ≤ n`, `Ω_m` and `Ω̄_m` have the same flip parity on every
variable. Starting in either phase on `F_0, …, F_m`, applying either complete string changes these
layers to the other phase. -/
theorem lemma_22 (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : m ≤ n) :
    (∀ x : Vx, (Omega m).count x % 2 = (OmegaBar m).count x % 2) ∧
    ∀ (σ : V n → Bool) (ε : Bool), InPhase σ m ε →
      InPhase ((Omega m).foldl flipX σ) m (!ε) ∧
      InPhase ((OmegaBar m).foldl flipX σ) m (!ε) := by sorry

end TwoOptAllExp.TSP.Supplement
