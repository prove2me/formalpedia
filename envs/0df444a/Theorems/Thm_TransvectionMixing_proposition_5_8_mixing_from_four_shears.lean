-- Prove2me | Theorems.Thm_TransvectionMixing_proposition_5_8_mixing_from_four_shears
-- name    : TransvectionMixing.proposition_5_8_mixing_from_four_shears
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:19.52368+00:00
-- url     : https://prove2.me/theorems/62f29967-ef70-4fe1-a6a3-11fc16395f2f
-- title:
--   Proposition 5.8 — mixing from four shears in $T_{\mathrm{shears}}(\eta)$ steps
-- statement:
--   Let $n\ge 256$ and $0<\eta\le 1/4$.
--
--   1. Let $0<u\le 1/4$ and $q\ge Q_{\mathrm{geom}}(H(T_{\mathrm{shears}}(\eta),\eta),n^2-1;u)$. For every fixed $X\in\mathrm{SL}_n(\mathbb F_q)$, a uniformly random skeleton $\sigma$ of length $T_{\mathrm{shears}}(\eta)$ satisfies
--   $$
--   \Pr_\sigma\bigl[\|K_\sigma(X,\cdot)-\pi\|_{TV}>u/8\bigr]\le\eta/4 .
--   $$
--   2. Taking $u=\eta$ gives $t^{(n)}_{\mathrm{mix}}(\eta)\le T_{\mathrm{shears}}(\eta)$: $d_{[n]\times[n]}(T_{\mathrm{shears}}(\eta))\le\eta$.
--   3. $T_{\mathrm{shears}}(\eta)\le 20n^2+24n\log\frac1{4\eta}$ and $T_{\mathrm{shears}}(\eta)\le 14n^2+80n\log\frac n\eta$.
--   4. $T_{\mathrm{shears}}(\eta)\le(8\log 2+o(1))n^2$ when $\log(n/\eta)=o(n)$: for every sequence $0<\eta_n\le 1/4$ with $\log(n/\eta_n)/n\to0$ and every $\delta>0$, eventually $T_{\mathrm{shears}}(\eta_n)\le(8\log 2+\delta)n^2$.
--
--   This gives rows 3–4 of the main theorem's table after projection to $\mathcal S$.
--
--   **Formalization Note** $K_\sigma(X,\cdot)$ and $\pi$ are compared through all $n^2$ entries, which identify a matrix.
--
--   Differences from the source:
--   - reading: t^{(n)}_mix(η) ≤ T_shears(η) (taking u = η) → d_{[n]×[n]}(T_shears(η)) ≤ η under q ≥ Q_geom(H(T_shears(η), η), n² − 1; η); reason: t_mix(η) = min{t : d(t) ≤ η}; d is nonincreasing (p.35), so the two are equivalent, and the proof establishes d(T_shears(η)) ≤ 3η/8 directly
--   - encoding: (8 log 2 + o(1))n² when log(n/η) = o(n) → for every sequence 0 < η_m ≤ 1/4 with log(m/η_m)/m → 0 and every δ > 0, eventually T_shears(η_m) ≤ (8 log 2 + δ)m²; reason: explicit quantifiers for the o(1)
--   - encoding: ‖K_σ(X, ·) − π‖_TV on SLₙ(𝔽_q) → d^σ_𝒮(X) with 𝒮 = [n] × [n]; reason: restriction to all entries is injective; same distance
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Proposition 5.8, eqs. (36)–(37), p.29

import Mathlib
import Definitions.Def_TransvectionMixing_dS
import Definitions.Def_TransvectionMixing_Tshears

namespace TransvectionMixing

open Filter Topology

/-- **Proposition 5.8** (mixing from four shears) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.3.3, p.29). Let `n ≥ 256` and
`0 < η ≤ 1/4`.

1. (eq. (36)) For `0 < u ≤ 1/4` and `q ≥ Q_geom(H(T_shears(η), η), n² − 1; u)`, for every
   fixed `X ∈ SLₙ(𝔽_q)` a random skeleton `σ` of length `T_shears(η)` satisfies
   `Pr_σ[‖K_σ(X, ·) − π‖_TV > u/8] ≤ η/4`.
2. Taking `u = η` gives `t^{(n)}_mix(η) ≤ T_shears(η)`, i.e.
   `d_{[n]×[n]}(T_shears(η)) ≤ η` when `q ≥ Q_geom(H(T_shears(η), η), n² − 1; η)`.
3. (eq. (37)) `T_shears(η) ≤ 20n² + 24n log(1/(4η))` and `T_shears(η) ≤ 14n² + 80n log(n/η)`.
4. (eq. (37), third line) `T_shears(η) ≤ (8 log 2 + o(1))n²` when `log(n/η) = o(n)`: for every
   sequence `0 < ηₙ ≤ 1/4` with `log(n/ηₙ)/n → 0` and every `δ > 0`, eventually
   `T_shears(ηₙ) ≤ (8 log 2 + δ)n²`.

**Formalization Note** `K_σ(X, ·)` and `π` are compared through all `n²` entries
(`𝒮 = [n] × [n]`), which identifies a matrix. -/
theorem proposition_5_8_mixing_from_four_shears (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (n : ℕ) (hn : 256 ≤ n) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) :
    (∀ u : ℝ, 0 < u → u ≤ 1 / 4 →
        Qgeom (Hdeg n (Tshears n η) η) ((n : ℝ) ^ 2 - 1) u ≤ Fintype.card F →
        ∀ X : Matrix.SpecialLinearGroup (Fin n) F,
          prob (fun σ : Skel n (Tshears n η) => u / 8 < dSigma F σ X Finset.univ) ≤ η / 4) ∧
      (Qgeom (Hdeg n (Tshears n η) η) ((n : ℝ) ^ 2 - 1) η ≤ Fintype.card F →
        dS F (Finset.univ : Finset (Fin n × Fin n)) (Tshears n η) ≤ η) ∧
      (Tshears n η : ℝ) ≤ 20 * (n : ℝ) ^ 2 + 24 * n * Real.log (1 / (4 * η)) ∧
      (Tshears n η : ℝ) ≤ 14 * (n : ℝ) ^ 2 + 80 * n * Real.log (n / η) ∧
      (∀ ηs : ℕ → ℝ, (∀ m, 0 < ηs m ∧ ηs m ≤ 1 / 4) →
        Tendsto (fun m : ℕ => Real.log (m / ηs m) / m) atTop (𝓝 0) →
        ∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in atTop, (Tshears m (ηs m) : ℝ) ≤ (8 * Real.log 2 + δ) * (m : ℝ) ^ 2) := by sorry

end TransvectionMixing
