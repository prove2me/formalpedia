-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_proposition_8_10
-- name    : SmallGainISS.OmegaPath.proposition_8_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:18.191035+00:00
-- url     : https://prove2.me/theorems/74584446-0b3d-4d4d-a6cb-a97e798247aa
-- title:
--   Proposition 8.10 — under $T\not\ge\mathrm{id}$, $\Omega(T)\cap S_r\neq\emptyset$ for every $r>0$
-- statement:
--   Let $n\ge1$ and let $T:\mathbb R^n_+\to\mathbb R^n_+$ be monotone and continuous with $T\not\ge\mathrm{id}$, i.e. for every $s\ne0$ it is not true that $s\le T(s)$. Let $S_r=\{s\in\mathbb R^n_+:s_1+\dots+s_n=r\}$. Then
--   $$\Omega(T)\cap S_r\neq\emptyset\qquad\text{for all } r>0,$$
--   where $\Omega(T)=\{s:T(s)<s\}$ with the strict inequality in every component.
--
--   The proof in the literature rests on the Knaster–Kuratowski–Mazurkiewicz theorem; the result is the topological input of Proposition 8.9.
--
--   **Formalization Note** The paper prints the hypothesis as "$T(s)\not\ge s$ for all $s\in\mathbb R^n_+$", which no map satisfies at $s=0$ (there $T(0)\ge0$). The statement uses the small gain condition for $s\ne0$, as on p. 12 and in Proposition 8.9. The case $n=0$ is excluded because $S_r$ is then empty.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 23, Proposition 8.10 (hypothesis read for s ≠ 0)

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Proposition 8.10 (p. 23), with the hypothesis read as (SGC): `T(s) ≱ s` for all `s ≠ 0`
(the printed "for all `s ∈ ℝⁿ₊`" fails at `s = 0`). For `T` monotone and continuous on
`ℝⁿ₊`, `n ≥ 1`, the set `Ω(T) ∩ S_r` is nonempty for every `r > 0`. -/
theorem proposition_8_10 {n : ℕ} (hn : 0 < n) (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0))
    (hmono : Monotone T) (hcont : Continuous T) (hsgc : SGC T) :
    ∀ r : ℝ≥0, 0 < r → (SmallGainISS.Lyapunov.Omega T ∩ sphereOne n r).Nonempty := by sorry

end SmallGainISS.OmegaPath
