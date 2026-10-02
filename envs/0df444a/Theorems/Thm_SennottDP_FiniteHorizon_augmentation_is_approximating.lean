-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_augmentation_is_approximating
-- name    : SennottDP.FiniteHorizon.augmentation_is_approximating
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:30:27.161632+00:00
-- url     : https://prove2.me/theorems/694e1ca0-333d-4d2a-93e4-13b6f6d369c4
-- title:
--   Proposition 2.5.6 — the augmentation (2.19) defines an approximating probability distribution
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$, let $(S_N)_{N \ge N_0}$ be finite nonempty subsets of $S$ increasing to $S$, and for $N \ge N_0$, $i \in S_N$, $a \in A_i$, $r \notin S_N$ let $(q_j(i,a,r,N))_{j \in S_N}$ be a probability distribution on $S_N$. Define
--   $$
--   P_{ij}(a;N) = P_{ij}(a) + \sum_{r \in S - S_N} P_{ir}(a)\, q_j(i,a,r,N), \qquad j \in S_N. \tag{2.19}
--   $$
--   Then (2.19) defines an approximating probability distribution on $S_N$:
--
--   1. $\sum_{j \in S_N} P_{ij}(a;N) = 1$ for $N \ge N_0$, $i \in S_N$, $a \in A_i$;
--   2. $\lim_{N \to \infty} P_{ij}(a;N) = P_{ij}(a)$ for all $i$, $a \in A_i$ and $j \in S$.
--
--   This is what makes every augmentation procedure an approximating sequence in the sense of Definition 2.5.1.
--
--   **Formalization Note** The right-hand side of (2.19) is `augProb` and is evaluated for every $N$; the limit in item 2 only involves $N$ large enough that $i, j \in S_N$ and $N \ge N_0$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 32, Proposition 2.5.6

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Proposition 2.5.6 (Sennott, p. 32). Let `S_N` (`N ≥ N₀`) be finite nonempty subsets of `S`
increasing to `S`, and let `q_j(i, a, r, N)` be augmentation distributions on `S_N`. Then
equation (2.19), `P_ij(a; N) = P_ij(a) + ∑_{r ∈ S − S_N} P_ir(a) q_j(i, a, r, N)`, defines an
approximating probability distribution on `S_N`: it sums to `1` over `S_N` for `N ≥ N₀`,
`i ∈ S_N`, `a ∈ A_i`, and `lim_{N → ∞} P_ij(a; N) = P_ij(a)` for every `j ∈ S` (2.17). -/
theorem augmentation_is_approximating {S Act : Type} [Countable S] (M : MDC S Act)
    (N₀ : ℕ) (SN : ℕ → Finset S) (hSN : MDC.IsStateApprox N₀ SN)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : M.IsAugmentation N₀ SN q) :
    (∀ N, N₀ ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, M.augProb SN q N i a j = 1) ∧
    (∀ i, ∀ a ∈ M.A i, ∀ j,
      Tendsto (fun N => M.augProb SN q N i a j) atTop (𝓝 (M.P i a j))) := by sorry

end SennottDP.FiniteHorizon
