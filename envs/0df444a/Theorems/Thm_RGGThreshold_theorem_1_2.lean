-- Prove2me | Theorems.Thm_RGGThreshold_theorem_1_2
-- name    : RGGThreshold.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:11.26398+00:00
-- url     : https://prove2.me/theorems/431966dc-770b-4bae-aa53-1fb10409334e
-- title:
--   Theorem 1.2 — $\mathrm{TV}(G(n,p),G(n,d,p))\le\varepsilon$ for $d\ge C_\varepsilon n^3p^3(\log p^{-1})^3$
-- statement:
--   Let $G(n,p)$ be the Erdős–Rényi graph and $G(n,d,p)$ the spherical random geometric graph: $x_1,\dots,x_n$ independent uniform on $\mathbb S^{d-1}$, with $i\ne j$ adjacent when $\langle x_i,x_j\rangle\ge c_{p,d}/\sqrt d$, the threshold chosen so that each edge has probability $p$. For two laws $\mu,\mu'$ on a finite set $\Omega$, $\mathrm{TV}(\mu,\mu')=\frac12\sum_{x\in\Omega}|\mu(x)-\mu'(x)|$.
--
--   For every $\varepsilon>0$ there exists a large constant $C_\varepsilon>0$ with the following property. Let $n$ be a large positive integer and $p\in(0,1)$ a probability with $1/3\ge p\ge n^{-1/5}(\log n)^A$, where $A$ is a large absolute constant. For every $d\ge C_\varepsilon n^3p^3(\log p^{-1})^3$,
--
--   $$
--   \mathrm{TV}\big(G(n,p),G(n,d,p)\big)\le\varepsilon .
--   $$
--
--   This resolves the distinguishability conjecture of Bubeck, Ding, Eldan and Rácz for $p\ge n^{-1/5}(\log n)^A$: above $d\asymp(np\log p^{-1})^3$ no test separates the two models.
--
--   **Formalization Note** The two laws are the published `RGGDetect.erLaw` and `RGGDetect.rggLaw`, and TV is the published `IsingLTL.BeliefProp.tvDist` of their point masses on the finite type of graphs on `Fin n`.
--
--   Differences from the source:
--
--   - reading: "where A is a large absolute constant" → ∃ A before ∀ ε; reason: absolute means A does not depend on ε; this is the stronger order
--   - reading: "Let n be a large positive integer" → ∃ N after C_ε, ∀ n ≥ N; reason: N may depend on ε
--   - encoding: A a large absolute (real) constant → A : ℕ, used as (log n)^A; reason: for n ≥ 3, raising A to ⌈A⌉ only shrinks the p-range, so the two forms are equivalent
--   - encoding: the threshold c_{p,d}/√d with P[⟨x_i,x_j⟩ ≥ c_{p,d}/√d] = p → any τ with capProb d τ = p; reason: for d ≥ 2 this τ is unique and equals c_{p,d}/√d; the Lean statement holds for every solution
--   - encoding: TV(G(n,p), G(n,d,p)) = ½ Σ_H |µ(H) − µ′(H)| → tvDist of the real point masses of erLaw and rggLaw on SimpleGraph (Fin n); reason: the same formula on the finite set of graphs
--   - encoding: vertices and coordinates 1, …, n → Fin n, numbered from 0; reason: index shift only; each statement shifts s accordingly
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Theorem 1.2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw
import Definitions.Def_RGGDetect_erLaw
import Definitions.Def_IsingLTL_BeliefProp_TVDist

open MeasureTheory

namespace RGGThreshold

/-- **Theorem 1.2** (Hunter–Milojević–Sudakov, *Distinguishability Threshold for Random Geometric Graphs*, arXiv:2607.22480, held version, sha256 1a398ef9…, Theorem 1.2, p.3 (PDF p.5)). For every `ε > 0` there exists a large
constant `C_ε > 0` with the following property. Let `n` be a large positive integer and `p ∈ (0, 1)`
a probability satisfying `1/3 ≥ p ≥ n^{-1/5}(log n)^A`, where `A` is a large absolute constant. For
every `d ≥ C_ε n³p³(log p⁻¹)³` we have `TV(G(n, p), G(n, d, p)) ≤ ε`.

**Formalization Note** `A` is absolute, so it is chosen before `ε`; "`n` large" is `∃ N` after
`C_ε`. `G(n, d, p)` is the spherical random geometric graph `RGGDetect.rggLaw n d τ`, which joins
`i ≠ j` when `⟨x_i, x_j⟩ ≥ τ`, for any `τ` with `P[⟨x_1, x_2⟩ ≥ τ] = p` (the paper's `c_{p,d}/√d`);
`G(n, p)` is `RGGDetect.erLaw n p`. `TV(μ, μ') = ½ ∑_H |μ(H) - μ'(H)|` over the finite set of graphs
on `Fin n`. `(log n)^A` uses a natural exponent. -/
theorem theorem_1_2 :
    ∃ A : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : ℝ, 0 < p → p ≤ 1 / 3 → (n : ℝ) ^ (-(1 / 5 : ℝ)) * Real.log n ^ A ≤ p →
    ∀ d : ℕ, C * (n : ℝ) ^ 3 * p ^ 3 * Real.log (1 / p) ^ 3 ≤ d →
    ∀ τ : ℝ, RGGDetect.capProb d τ = p →
    IsingLTL.BeliefProp.tvDist (fun H : SimpleGraph (Fin n) => (RGGDetect.erLaw n p).real {H})
      (fun H : SimpleGraph (Fin n) => (RGGDetect.rggLaw n d τ).real {H}) ≤ ε := by sorry

end RGGThreshold
