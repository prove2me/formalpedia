-- Prove2me | Theorems.Thm_QubitFreqSensing_lemma_5_9
-- name    : QubitFreqSensing.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:20.307451+00:00
-- url     : https://prove2.me/theorems/b467d4d1-9ad8-49a3-a32b-e3e1e3a52fdf
-- title:
--   Lemma 5.9 — Möbius perturbations do not decrease correlations on average and double a small one
-- statement:
--   Let $N\ge1$, $\omega_1,\dots,\omega_N>0$, $\eta\in(0,1/16)$, $r=\eta/\sqrt N$ and $u\in\mathbb T$.
--
--   1. For all $i,j\in[N]$ with $\langle g_j,u\rangle\ne0$,
--   $$
--   \mathbb E_{|z|=r}\left[\log\frac{|\langle g_j,\Phi^{(i)}_z u\rangle|}{|\langle g_j,u\rangle|}\right]\ \ge\ 0 .
--   $$
--   2. Let $C\ge4$ and $c\le\eta/32$. If $\|u\|^2\le1/(2C)$ and $0<|\langle g_i,u\rangle|\le c/\sqrt N$, then
--   $$
--   \mathbb E_{|z|=r}\left[\log\frac{|\langle g_i,\Phi^{(i)}_z u\rangle|}{|\langle g_i,u\rangle|}\right]\ \ge\ \log 2 .
--   $$
--
--   Here $\mathbb E_{|z|=r}$ averages over $z=re^{i\theta}$, $\theta$ uniform in $[0,2\pi]$. The first part follows from the subharmonicity of $\log|\cdot|$ (Corollary 5.3). The second follows from Jensen's formula once $z\mapsto\langle g_i,\Phi^{(i)}_z u\rangle$ is shown to have a zero in $|z|<r/2$.
--
--   Differences from the source:
--   - reading: the second part with 'our choice of C' (C > 0 sufficiently large) → C ≥ 4; reason: the proof states 'where we used that C ≥ 4' (p.20)
--   - encoding: the first part for all i, j → for all i, j with ⟨g_j, u⟩ ≠ 0; reason: the ratio |⟨g_j, Φ_z u⟩|/|⟨g_j, u⟩| is undefined when ⟨g_j, u⟩ = 0
--   - encoding: E_{|z|=r} of log |·| with log 0 = −∞ → Real.circleAverage of Real.log (Real.log 0 = 0); reason: z ↦ ⟨g_j, Φ_z u⟩ is holomorphic and nonzero at 0, so it vanishes on a finite, null subset of the circle
--   - encoding: 𝕋 = L² functions [0, 2π] → 𝔻 → measurable u : ℝ → ℂ with ‖u x‖ < 1 on [0, 2π] (discFns); reason: every quantity depends only on the a.e. class (a Lebesgue-measurable u agrees a.e. with a Borel one, changed to 0 on a null set); L² is automatic for |u| < 1
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Lemma 5.9, p.19 (PDF p.19); proof pp.19–20

import Mathlib
import Definitions.Def_QubitFreqSensing_Potential
import Definitions.Def_QubitFreqSensing_Mobius

namespace QubitFreqSensing

/-- **Lemma 5.9** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Lemma 5.9,
p.19). "Let r = η/√N for η ∈ (0, 1/16) and let u ∈ 𝕋. Then, for all i, j ∈ [N], we have that
E_{|z|=r}[log(|⟨gj, Φz^{(i)}u⟩| / |⟨gj, u⟩|)] ≥ 0. Moreover, suppose u ∈ 𝕋 satisfies
∥u∥² ≤ 1/(2C), and 0 < |⟨gi, u⟩| ≤ c/√N, for c ≤ η/32. Then we have that
E_{|z|=r}[log(|⟨gi, Φz^{(i)}u⟩| / |⟨gi, u⟩|)] ≥ log 2."

**Formalization Note** `E_{|z|=r}` is `Real.circleAverage · 0 r`. The first part assumes
`⟨g_j, u⟩ ≠ 0`, without which its ratio is undefined. The second part assumes `C ≥ 4`, used in the
proof ("where we used that C ≥ 4", p.20). `Real.log` returns `0` at `0`, but `z ↦ ⟨g_j, Φ_z u⟩` is
holomorphic and nonzero at `0`, so it vanishes at finitely many points of the circle, a null set.
The standing assumptions of §5 (`N ≥ 1`, `ω_i > 0`) are hypotheses. -/
theorem lemma_5_9 (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → ℝ) (hω : ∀ i, 0 < ω i)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 16) (u : ℝ → ℂ) (hu : u ∈ discFns) :
    (∀ i j : Fin N, inner2pi (gcos ω j) u ≠ 0 →
      0 ≤ Real.circleAverage (fun z =>
        Real.log (‖inner2pi (gcos ω j) (Phi ω i z u)‖ / ‖inner2pi (gcos ω j) u‖)) 0
        (η / Real.sqrt N)) ∧
    (∀ (C c : ℝ), 4 ≤ C → c ≤ η / 32 → normSq2pi u ≤ 1 / (2 * C) → ∀ i : Fin N,
      0 < ‖inner2pi (gcos ω i) u‖ → ‖inner2pi (gcos ω i) u‖ ≤ c / Real.sqrt N →
      Real.log 2 ≤ Real.circleAverage (fun z =>
        Real.log (‖inner2pi (gcos ω i) (Phi ω i z u)‖ / ‖inner2pi (gcos ω i) u‖)) 0
        (η / Real.sqrt N)) := by sorry

end QubitFreqSensing
