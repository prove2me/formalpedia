-- Prove2me | Theorems.Thm_TractableComposite_proposition_1
-- name    : TractableComposite.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:12.342438+00:00
-- url     : https://prove2.me/theorems/48dd48b6-f3a5-4139-9f29-461c30dfafe0
-- title:
--   Proposition 1 (Prop. 5 in [17]) — the lifting $\bar s=\Gamma_J(\bar u)$ lies on the face $F_J$
-- statement:
--   Let $a$ have strictly increasing rows, let $\bar u\in P$ and let $\bar s$ be its lifting (4), so that $(\bar u,\bar s)\in PQ'$. Put $J_i=\{j\mid\bar u_{ij}=\bar s_{ij}\}$. Then
--
--   1. $\bar s=\Gamma_J(\bar u)$;
--   2. every $s\in Q$ satisfies $s\ge\Gamma_J(s)$ (componentwise);
--   3. $F_J=\{s\in Q\mid s\le\Gamma_J(s)\}$;
--   4. $\bar s\in F_J$.
--
--   The proposition locates the face of $Q$ that the lifted point lies on; Theorem 2's algorithm works on that face.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - generalization: 0 ≤ a_i0 < ⋯ < a_in ≤ 1 (normalization of (1)) → any strictly increasing rows a_i; reason: the paper's normalization is without loss of generality (p.3) and §3.1 never uses the bounds; every normalized a is an instance
--   - encoding: conc(ξᵢ)(aᵢⱼ; ūᵢ), the concave envelope of the discrete function ξᵢ at aᵢⱼ → liftS: supremum of ∑ₖ wₖ ūᵢₖ over weights w ≥ 0 with ∑ₖ wₖ = 1 and ∑ₖ wₖ aᵢₖ = aᵢⱼ; reason: ξᵢ is −∞ off the points aᵢₖ, so only convex combinations of those points count; same values
--   - encoding: (ū, s̄) ∈ PQ′ → ū ∈ P with s̄ = liftS a ū; reason: (4) defines PQ′ as the graph of this lifting
--   - encoding: F_J is the face of Q defined by the inequalities s ≤ Γ_J(s) → the set equality F_J = {s ∈ Q | s ≤ Γ_J(s)}; reason: that F_J is a face of Q is stated on p.5; the content of the clause is this description of it
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 1, p.5

import Mathlib
import Definitions.Def_TractableComposite_P
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_FJ
import Definitions.Def_TractableComposite_gammaJ
import Definitions.Def_TractableComposite_liftS
import Definitions.Def_TractableComposite_Jof

namespace TractableComposite

/-- **Proposition 1 (Proposition 5 in [17])**, p.5. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Proposition 1, p.5.

Let `(ū, s̄) ∈ PQ'` (i.e. `ū ∈ P` and `s̄` is its lifting (4)) and `Jᵢ = {j | ūᵢⱼ = s̄ᵢⱼ}`. Then
`s̄ = Γ_J(ū)`; every `s ∈ Q` satisfies `s ≥ Γ_J(s)`; `F_J` is the face of `Q` cut out by `s ≤ Γ_J(s)`;
and `s̄ ∈ F_J`.

**Formalization Note.** Standing data of §2–§3: `d, n ≥ 1`, each row `aᵢ` strictly increasing (reading
R9: the normalization `0 ≤ aᵢ₀`, `aᵢₙ ≤ 1` is not imposed). Inequalities between points are
coordinatewise. -/
theorem proposition_1 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (a : Fin d → Fin (n + 1) → ℝ) (ha : ∀ i, StrictMono (a i)) (u : Fin d → Fin (n + 1) → ℝ) (hu : u ∈ P a) :
    liftS a u = gammaJ a (Jof a u) u ∧
    (∀ s ∈ Q a, ∀ i j, gammaJ a (Jof a u) s i j ≤ s i j) ∧
    FJ a (Jof a u) = {s | s ∈ Q a ∧ ∀ i j, s i j ≤ gammaJ a (Jof a u) s i j} ∧
    liftS a u ∈ FJ a (Jof a u) := by sorry

end TractableComposite
