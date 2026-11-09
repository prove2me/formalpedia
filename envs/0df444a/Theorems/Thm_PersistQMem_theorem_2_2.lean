-- Prove2me | Theorems.Thm_PersistQMem_theorem_2_2
-- name    : PersistQMem.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:49.422002+00:00
-- url     : https://prove2.me/theorems/b92a0796-f4cd-462f-8b1a-042b4b423f1d
-- title:
--   Theorem 2.2 (Finite testing bound) — $N\ge4(1-\theta)(1-2\delta)^2/((3-4\delta)\theta^2B_K)$
-- statement:
--   Fix the data of Definition 2.1, an integer $K\ge1$ and $0<\theta<1$. For $j\in\{1,\dots,M\}$ and $z\in\{-1,1\}$ put
--   $$\rho_{j,z}=\frac{I_D+z\theta G_j}D .\tag{4}$$
--   The label $(j,z)$ is chosen once with probability $p_j/2$ and the same source is used for all copies. Consider any receiver using ordinary independent copies, a retained quantum system of dimension at most $K$ (every register retained between accesses counts toward $K$, and the memory may stay coherent for the whole run), unlimited classical records in a general measurable record space, and arbitrary adaptive complete instruments whose choice depends measurably on the history, using at most $N$ copies. If a single decoder event $E$ satisfies, for some $0\le\delta<1/2$,
--   $$\Pr_\tau(E)\le\delta,\qquad\sum_j\frac{p_j}2\sum_{z=\pm1}\Pr_{\rho_{j,z}}(E)\ge1-\delta,\tag{5}$$
--   then
--   $$N\ge\frac{4(1-\theta)(1-2\delta)^2}{(3-4\delta)\theta^2B_K}.\tag{6}$$
--
--   The bound charges only the retained dimension $K$, through $B_K=\zeta(K)+(2K-2)\beta$, against arbitrary adaptivity and unlimited memory lifetime; estimation lower bounds (Corollary 2.3 and §§7–9) follow from it.
--
--   Differences from the source:
--   - encoding: receiver with retained dimension ≤ K on every branch, at most N copies, measurable instruments and controls on product σ-algebras of histories, terminal effects Q_h → Protocol X L K D (memory Fin K, rounds 0,…,N−1 of a round sequence, s-finite reference kernels on Fin t → X with jointly measurable Kraus densities complete for every history) and DecoderEvent X K N (entrywise measurable effect field); Pr_ρ(E) = prob P E ρ = ∫ Re Tr(Q_h ω^ρ_N(h)) dν_N; reason: registers of dimension ≤ K embed in C^K and early stopping is idling (pp.15, 28); per-round record spaces embed in one disjoint union; every measurable adaptive instrument has such a density (§6.6, (67)–(74)) and completeness off a ν-null set changes no probability
--   - reading: “general measurable record spaces” (Theorem 2.2) / “standard Borel outcome spaces” (§5.3, p.15) → an arbitrary measurable space X; reason: the theorem's own wording; the more general of the two readings, which contains every standard Borel space
--   - encoding: z ∈ {−1, 1} → z : Bool with zsign true = 1, zsign false = −1; reason: Lean convention; same two signs
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Theorem 2.2, (4)–(6), p.4 (PDF p.7); proof §6.5, pp.25–27 and §6.6, pp.27–28

import Mathlib
import Definitions.Def_PersistQMem_ProfileData
import Definitions.Def_PersistQMem_Protocol

open scoped Matrix ComplexOrder
open MeasureTheory

namespace PersistQMem

/-- **Theorem 2.2 (Finite testing bound), p.4** (Tao, Shen, *Structural Lower Bounds for Quantum
Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, Theorem 2.2, (4)–(6), p.4). Fix the data of Definition 2.1, an integer `K ≥ 1`,
and `0 < θ < 1`; put `ρ_{j,z} = (I_D + zθG_j)/D` (4), with `(j, z)` drawn once with probability
`p_j/2` and the same source used for all copies. Consider any receiver with a retained quantum
memory of dimension at most `K`, unlimited classical records in a general measurable record space,
and arbitrary adaptive complete instruments given by measurable kernels on the product σ-algebras
of successive histories, using at most `N` copies. If a single decoder event `E` satisfies, for some
`0 ≤ δ < 1/2`, (5) `Pr_τ(E) ≤ δ` and `Σ_j (p_j/2) Σ_{z=±1} Pr_{ρ_{j,z}}(E) ≥ 1 − δ`, then
(6) `N ≥ 4(1 − θ)(1 − 2δ)² / ((3 − 4δ) θ² B_K)`.

**Formalization Note.** The receiver is `Protocol X L K D` (memory `C^K` on every branch, instruments
as s-finite reference kernels with jointly measurable Kraus densities, complete for every history),
the event is `DecoderEvent X K N`, and `Pr_ρ(E) = prob P E ρ`. The protocol and the event are
fixed before the source. `z ∈ {−1, 1}` is a Boolean through `zsign`. -/
theorem theorem_2_2 {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (N : ℕ) (X : Type) [MeasurableSpace X]
    (L : Type) [Fintype L] (P : Protocol X L K D) (E : DecoderEvent X K N)
    (h5τ : prob P E (tau D) ≤ δ)
    (h5ρ : 1 - δ ≤ ∑ j, p j / 2 * ∑ z : Bool, prob P E (rhoAlt θ (G j) z)) :
    4 * (1 - θ) * (1 - 2 * δ) ^ 2 / ((3 - 4 * δ) * θ ^ 2 * budget G p K) ≤ N := by sorry

end PersistQMem
