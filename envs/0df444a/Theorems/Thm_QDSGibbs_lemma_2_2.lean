-- Prove2me | Theorems.Thm_QDSGibbs_lemma_2_2
-- name    : QDSGibbs.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:32.551673+00:00
-- url     : https://prove2.me/theorems/7b0b516f-cc20-4bc3-8b1c-c1acf6fc979f
-- title:
--   Lemma 2.2 — elementary transport estimates
-- statement:
--   Let $\Lambda$ be a finite set of $N$ sites with local dimensions $d_i\ge2$, let $\|\cdot\|_{W_1}$ be the transport norm (2.9) and $D_\Psi(j)$ the influence coefficient (2.11).
--
--   1. For traceless Hermitian $X$, $\ \frac12\|X\|_1\le\|X\|_{W_1}\le\frac N2\|X\|_1$.
--   2. If moreover $\mathrm{Tr}_jX=0$ for some site $j$, then $\|X\|_{W_1}=\|X\|_1/2$.
--   3. If $\emptyset\ne R\subseteq\Lambda$, $Y=Y^*$, $\mathrm{Tr}_RY=0$, and $j_1,\dots,j_m$ enumerate $R$, then
--
--   $$
--   \|Y\|_{W_1}\le\sum_{b=0}^{m-1}\|\mathrm{Tr}_{j_1,\dots,j_b}Y\|_1\le|R|\,\|Y\|_1,\qquad \mathrm{Tr}_\emptyset=\mathrm{id}.
--   $$
--
--   4. For traceless Hermitian $Y$ and any $S\subseteq\Lambda$, $\ \|Y\|_{W_1}\le|S|\,\|Y\|_1+\|\mathrm{Tr}_SY\|_{W_1}$, the last norm taken on $\Lambda\setminus S$ (zero when $S=\Lambda$).
--   5. A channel $\Psi$ supported away from $j$ has $D_\Psi(j)=1$.
--   6. If two channels $\Phi,\Psi$ are supported on $R$, then for Hermitian $X$
--
--   $$
--   \|(\Phi-\Psi)(X)\|_{W_1}\le|R|\,\|\Phi-\Psi\|_\diamond\,\|X\|_1 .
--   $$
--
--   These estimates convert trace-norm and diamond-norm bounds into transport bounds; they are used in every influence estimate of the paper.
--
--   **Formalization Note** $\|\mathrm{Tr}_SY\|_1$ is the trace norm of $\mathrm{ptr}_SY$ divided by $\dim\mathcal H_S$, and the $W_1$ norm on $\Lambda\setminus S$ is the full-space $W_1$ norm of $\mathbb 1_S/\dim\mathcal H_S\otimes\mathrm{Tr}_SY$.
--
--   Differences from the source:
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - encoding: $\|\mathrm{Tr}_SY\|_{W_1}$ taken on $\Lambda\setminus S$ → the full-space $W_1$ norm of $(\dim\mathcal H_S)^{-1}\,\mathrm{ptr}_S Y$; reason: tensoring a decomposition with the normalized identity, or tracing one out, gives the same infimum; for $S=\Lambda$ both are $0$
--   - encoding: "$j_1,\dots,j_m$ enumerate $R$" → an injective map $e$ from $\{0,\dots,|R|-1\}$ into $R$, with $\{j_1,\dots,j_b\}$ the image of $\{0,\dots,b-1\}$; reason: the same enumerations
--   - encoding: "a channel supported on $R$" (a channel on $\mathcal B(\mathcal H_R)$ tensored with the identity on $R^c$, p.12); "supported away from $j$" → `IsChannel Φ ∧ MapSupportedOn R Φ` (an explicit kernel on $R$-configurations); "away from $j$" is `MapSupportedOn (univ.erase j)`; reason: the same maps, written entrywise
--   - reading: local dimensions $2\le d_i\le d$ (standing, §2.1) → local dimensions $d_i\ge2$; reason: the upper bound $d$ plays no role
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 2.2, pp.13–14

import Mathlib
import Definitions.Def_QDSGibbs_IsChannel
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Lemma 2.2 (Elementary transport estimates)** (arXiv:2610.03578, held file sha256 ede55815…,
Lemma 2.2, pp.13–14). On `Λ = {0, …, N−1}` with local dimensions `d_i ≥ 2`:
1. `½‖X‖₁ ≤ ‖X‖_{W1} ≤ (N/2)‖X‖₁` for traceless Hermitian `X` (2.12);
2. if moreover `Tr_j X = 0` for some `j`, then `‖X‖_{W1} = ‖X‖₁/2`;
3. if `∅ ≠ R`, `Y = Y^*`, `Tr_R Y = 0` and `j_1, …, j_m` enumerate `R`, then
   `‖Y‖_{W1} ≤ Σ_{b=0}^{m−1} ‖Tr_{j_1…j_b} Y‖₁ ≤ |R| ‖Y‖₁` (2.13), `Tr_∅ = id`;
4. `‖Y‖_{W1} ≤ |S| ‖Y‖₁ + ‖Tr_S Y‖_{W1}` for traceless Hermitian `Y` and any `S` (2.14);
5. a channel supported away from `j` has `D_Ψ(j) = 1`;
6. for channels `Φ, Ψ` supported on `R` and Hermitian `X`,
   `‖(Φ − Ψ)(X)‖_{W1} ≤ |R| ‖Φ − Ψ‖⋄ ‖X‖₁` (2.15).

**Formalization Note** `‖Tr_{R_b} Y‖₁` is `ptrNorm R_b Y`, `R_b = {e 0, …, e (b−1)}`. The norm
`‖Tr_S Y‖_{W1}` "taken on `Λ ∖ S`" is the full-space `w1` of `1_S/dim H_S ⊗ Tr_S Y`, i.e.
`w1 ((dim H_S)⁻¹ • ptr S Y)` (the same value: tensor a decomposition with the normalized identity, or
trace one out); for `S = Λ` it is `w1 0 = 0`. "Supported on `R`" is `MapSupportedOn R`, "away from
`j`" is `MapSupportedOn (univ.erase j)`. `w1`, `D` and `‖·‖⋄` are `ℝ≥0∞`-valued. -/
theorem lemma_2_2 {N : ℕ} (d : Fin N → ℕ) (hd : ∀ i, 2 ≤ d i) :
    (∀ X : Op d, X.IsHermitian → X.trace = 0 →
      ENNReal.ofReal (traceNorm X / 2) ≤ w1 X ∧
        w1 X ≤ ENNReal.ofReal ((N : ℝ) / 2 * traceNorm X)) ∧
    (∀ X : Op d, X.IsHermitian → ∀ j : Fin N, ptr {j} X = 0 →
      w1 X = ENNReal.ofReal (traceNorm X / 2)) ∧
    (∀ R : Finset (Fin N), R.Nonempty → ∀ Y : Op d, Y.IsHermitian → ptr R Y = 0 →
      ∀ e : Fin R.card → Fin N, Function.Injective e → (∀ b, e b ∈ R) →
        w1 Y ≤ ENNReal.ofReal (∑ b : Fin R.card,
            ptrNorm ((Finset.univ.filter fun c : Fin R.card => c < b).image e) Y) ∧
        ∑ b : Fin R.card, ptrNorm ((Finset.univ.filter fun c : Fin R.card => c < b).image e) Y ≤
          (R.card : ℝ) * traceNorm Y) ∧
    (∀ Y : Op d, Y.IsHermitian → Y.trace = 0 → ∀ S : Finset (Fin N),
      w1 Y ≤ ENNReal.ofReal ((S.card : ℝ) * traceNorm Y) + w1 (((dimOf d S : ℂ))⁻¹ • ptr S Y)) ∧
    (∀ Ψ : Op d → Op d, IsChannel Ψ → ∀ j : Fin N, MapSupportedOn (Finset.univ.erase j) Ψ →
      influence Ψ j = 1) ∧
    (∀ R : Finset (Fin N), R.Nonempty → ∀ Φ Ψ : Op d → Op d, IsChannel Φ → IsChannel Ψ →
      MapSupportedOn R Φ → MapSupportedOn R Ψ → ∀ X : Op d, X.IsHermitian →
        w1 (Φ X - Ψ X) ≤
          (R.card : ℝ≥0∞) * diamondNorm (fun Y => Φ Y - Ψ Y) * ENNReal.ofReal (traceNorm X)) := by sorry

end QDSGibbs
