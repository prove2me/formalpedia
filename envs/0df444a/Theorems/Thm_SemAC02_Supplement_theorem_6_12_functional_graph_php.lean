-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_6_12_functional_graph_php
-- name    : SemAC02.Supplement.theorem_6_12_functional_graph_php
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:51:32.638505+00:00
-- url     : https://prove2.me/theorems/de22e49c-2045-452a-b5da-2613136bd240
-- title:
--   Theorem 6.12 — functional graph PHP needs semantic ΣΠΣ-PC size 2^{Ω(n)}
-- statement:
--   Fix positive integers $\Delta_{L,0},\Delta_{R,0}$ and constants $\delta_0>3$ and $\gamma>0$. There are $c>0$ and $n_0$, depending only on these parameters, such that for $n\ge n_0$ the following holds. Let $G$ have $n+1$ pigeons and $n$ holes, left degree at most $\Delta_{L,0}$, right degree at most $\Delta_{R,0}$, and be a $(\gamma n,\delta_0)$-boundary expander, and let $M$ be any matching covering all holes. Every arity-2 semantic ΣΠΣ-PC refutation $\pi$ of $\mathrm{FPHP}(G+M)$ over $\mathbb F_2$ satisfies
--
--   $$
--   S(\pi)\ge2^{cn},
--   $$
--
--   and the same bound holds for its total ΣΠΣ-size.
--
--   Restriction gives the same lower bound for the complete principle $\mathrm{FPHP}^{n+1}_n$ (Corollary 6.13).
--
--   **Formalization Note** $M=\{(\mu(v),v)\}$ for an injective $\mu$ from holes to pigeons; its edges need not be edges of $G$. Total ΣΠΣ-size is `csize`.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - encoding: size of a proof: distinct rooted subcircuits, sharing across lines → csize: distinct subterms of the lines; reason: a circuit term with equal subterms identified is the DAG with maximal sharing
--   - encoding: 2^{Ω(n)}, the constant depending only on the graph parameters → ∃ c > 0, ∃ n₀ after (Δ_{L,0}, Δ_{R,0}, δ₀, γ), ∀ n ≥ n₀; reason: asymptotic notation as explicit quantifiers
--   - encoding: matching M covering all holes → injective μ : Fin n → Fin (n+1), M = {(μ v, v)}; reason: a matching covering every hole is the same as such an injection
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 6.12, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_expansionRank
import Definitions.Def_SemAC02_Supplement_fphpG

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 6.12 (Functional graph PHP)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret,
*Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
Theorem 6.12, p.46): fix positive integers `Δ_{L,0}`, `Δ_{R,0}` and constants `δ₀ > 3` and
`γ > 0`. Suppose that `G` has `n + 1` pigeons, `n` holes, left degree at most `Δ_{L,0}`, right
degree at most `Δ_{R,0}`, and is a `(γn, δ₀)`-boundary expander. For any matching `M` covering all
holes, every semantic ΣΠΣ-PC refutation `π` of `FPHP(G + M)` satisfies `S(π) ≥ 2^{Ω(n)}`. The
implicit constant depends only on the fixed graph parameters. The same lower bound holds for total
ΣΠΣ-size.

**Formalization Note** `2^{Ω(n)}` is `2^{cn}` for all `n ≥ n₀`, with `c > 0` and `n₀` depending
only on `(Δ_{L,0}, Δ_{R,0}, δ₀, γ)`. The matching `M = {(μ v, v) : v ∈ [n]}` is given by an
injective `μ : [n] → [n+1]` (it covers every hole once; its edges need not be edges of `G`).
`FPHP(G + M)` is over `𝔽₂` (Definition 6.6). The total ΣΠΣ-size is the `C`-size `csize`. -/
theorem theorem_6_12_functional_graph_php (ΔL0 ΔR0 : ℕ) (hΔL : 0 < ΔL0) (hΔR : 0 < ΔR0)
    (δ₀ γ : ℝ) (hδ : 3 < δ₀) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ G : PCNonBool.BipGraph (Fin (n + 1)) (Fin n),
        (∀ u, (PCNonBool.nbrOn G Finset.univ u).card ≤ ΔL0) →
        (∀ v, (Finset.univ.filter (fun u => G.Adj u v)).card ≤ ΔR0) →
        IsBdryExp G (γ * n) δ₀ →
        ∀ μ : Fin n → Fin (n + 1), Function.Injective μ →
        ∀ π : List (ACirc (ZMod 2) (Edge (addMatching G μ))),
          IsSemPCRef IsSPS Set.univ (polyAx (fphpG (addMatching G μ))) π →
          (2 : ℝ) ^ (c * n) ≤ topS Set.univ π ∧ (2 : ℝ) ^ (c * n) ≤ csize π := by sorry

end SemAC02.Supplement
