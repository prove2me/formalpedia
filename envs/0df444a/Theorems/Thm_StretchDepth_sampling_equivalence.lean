-- Prove2me | Theorems.Thm_StretchDepth_sampling_equivalence
-- name    : StretchDepth.sampling_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:39.148916+00:00
-- url     : https://prove2.me/theorems/b718ca51-6684-4290-a29b-c5cb502ad605
-- title:
--   §2 — the two samplings of $\mathcal R^{n,N}_p$ agree
-- statement:
--   Let $p\in[0,1]$. Sample $\rho\sim\mathcal R^{n,N}_p$ directly, or sample $G:\{0,1\}^n\to\{0,1\}^N$ uniformly, then $S\subseteq\{0,1\}^n$ including each input independently with probability $p$, and set $\rho=G|_{\overline S}$. Both give the same law: for each partial assignment $\rho$,
--   $$
--   \Pr_{\mathcal R^{n,N}_p}[\rho]=\Pr_{G,S}[G|_{\overline S}=\rho].
--   $$
--   This identifies the distribution of Lemma 1 with the distribution of the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: rho = G|_{S̄} with S the free set (overline on the rendered p.13, p.20) → freeOn G S; reason: notation only, the same partial assignment
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), §2, p.13

import Definitions.Def_StretchDepth_PartialAssign

namespace StretchDepth

/-- **§2: the two samplings of `R^{n,N}_p` agree.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), §2, p.13: "Equivalently, we sample G : {0, 1}n → {0, 1}N uniformly at random, then sample
S ⊆ {0, 1}n by including each w ∈ {0, 1}n with probability p, and finally set ρ = G|_{S̄}."

**Formalization Note.** `G|_{S̄}` is `freeOn G S`, with `S` the free set (see `freeOn`). -/
theorem sampling_equivalence {n N : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : PartialAssign n N) :
    restrWeight p ρ = probGS p fun G S => freeOn G S = ρ := by sorry

end StretchDepth
