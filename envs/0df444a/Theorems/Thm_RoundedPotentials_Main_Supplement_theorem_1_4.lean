-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_theorem_1_4
-- name    : RoundedPotentials.Main.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:08:31.486499+00:00
-- url     : https://prove2.me/theorems/5c44e9d4-f5bb-4b6b-a3cc-6be09333d8d0
-- title:
--   Theorem 1.4 — Broadcast proof-labeling (Corollary 4.5)
-- statement:
--   Consider directed or undirected networks with arbitrary nonnegative integer capacities, distinct identifiers, terminals $s\ne t$, and a connected communication graph. An integer $p\ge0$ is the claimed value.
--
--   1. **Upper bound.** There is one local decision rule $D$ with the following property. For every exponent $K$ there is a constant $C$ such that, for every such network and every $p\ge0$:
--      - if $\mathrm{MaxFlow}(s,t)=p$ and all identifiers are below $n^K$ (that is, they have $O(\log n)$ bits), then some labelling with at most $C(\lfloor\log_2n\rfloor+\lfloor\log_2(p+1)\rfloor+1)$ bits per vertex makes every vertex accept;
--      - if $\mathrm{MaxFlow}(s,t)\ne p$, then every labelling makes some vertex reject.
--   2. **Optimality for $p\ge n^{\Omega(1)}$.** For every $\delta>0$ there are $\kappa>0$ and $n_0$ such that, for all $n\ge n_0$ and $p\ge n^\delta$, every decision rule that is sound on undirected networks with identifiers $0,\dots,n-1$ has the following defect: some true instance in that class has every accepting labelling using a label of at least
--   $$\kappa\bigl(\log_2 n+\log_2(p+1)\bigr)\text{ bits}.$$
--
--   This gives optimal labels for $p\ge n^{\Omega(1)}$, which answers the question of Korman, Kutten and Peleg on optimal bounds for flow verification.
--
--   **Formalization Note** Undirected networks are those in which every arc has its reverse with the same capacity. A vertex sees only its own local view (`Broadcast`), and in particular does not know $n$.
--
--   Differences from the source:
--   - encoding: undirected networks → networks whose arcs come in reverse pairs of equal capacity; reason: the source's own reduction ("treating each edge as two opposite edges of the same capacity")
--   - reading: identifiers of O(log n) bits; O(log n + log(p+1)) bits per vertex → one decision rule for all n, p; for every K, identifiers below n^K and labels of at most C_K(⌊log₂ n⌋+⌊log₂(p+1)⌋+1) bits; reason: explicit form of the O-bounds
--   - generalization: soundness on networks with O(log n)-bit identifiers → soundness for every network with distinct identifiers; reason: the scheme's check id(v) < N_id needs no bound; restricting the identifiers gives the source's claim
--   - reading: "For p ≥ n^{Ω(1)}, this is optimal up to constant factors" → ∀ δ > 0 ∃ κ > 0, n₀: for n ≥ n₀ and p ≥ n^δ, every rule sound on undirected networks with identifiers 0, …, n−1 has a true instance in that class all of whose accepting labellings use a label of ≥ κ(log₂ n + log₂(p+1)) bits; reason: the asymptotic meaning of the optimality claim, for the smallest class, which implies it for directed networks and arbitrary identifiers
--   - generalization: lower bound for correct schemes → only soundness on the class is assumed; an incomplete rule also satisfies the conclusion; reason: a correct scheme is sound, so this implies the source's lower bound
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 6, Theorem 1.4

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Broadcast

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main

theorem theorem_1_4 :
    -- upper bound: one decision rule, labels of `O(log n + log(p + 1))` bits
    (∃ D : LocalView → Bool, ∀ K : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (G : BNet n), G.Valid → ∀ p : ℕ,
        ((G.MaxFlowIs p → (∀ v, G.id v < n ^ K) →
            ∃ ℓ : Fin n → List Bool,
              (∀ v, (ℓ v).length ≤ C * (Nat.log 2 n + Nat.log 2 (p + 1) + 1)) ∧
              AllAccept D G p ℓ) ∧
         (¬ G.MaxFlowIs p → ∀ ℓ : Fin n → List Bool, ∃ v, D (view G p ℓ v) = false))) ∧
    -- optimality for `p ≥ n^δ`, already for undirected networks with identifiers `0, …, n − 1`
    (∀ δ : ℝ, 0 < δ → ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, (n : ℝ) ^ δ ≤ p → ∀ D : LocalView → Bool,
        (∀ G : BNet n, G.Valid → G.Undirected → G.id = (fun v => v.val) →
          ¬ G.MaxFlowIs p → ∀ ℓ : Fin n → List Bool, ∃ v, D (view G p ℓ v) = false) →
        ∃ G : BNet n, G.Valid ∧ G.Undirected ∧ G.id = (fun v => v.val) ∧ G.MaxFlowIs p ∧
          ∀ ℓ : Fin n → List Bool, AllAccept D G p ℓ →
            ∃ v, κ * (Real.logb 2 n + Real.logb 2 (p + 1)) ≤ (ℓ v).length) := by sorry

end RoundedPotentials.Main.Supplement
