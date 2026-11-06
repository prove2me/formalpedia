-- Prove2me | Theorems.Thm_PolarizedLearning_expectedPosterior_props
-- name    : PolarizedLearning.expectedPosterior_props
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:47.567864+00:00
-- url     : https://prove2.me/theorems/8afa08a7-eb9c-47c0-b234-8adf031af233
-- title:
--   Proof of Theorems 1–2, p. ec2 — $f(\pi,L)<\pi<f(\pi,H)$, $f(0,\cdot)=0$, $f(1,\cdot)=1$, continuity and bounds
-- statement:
--   Let $1/2<\alpha<1$ and let $f$ be the expected posterior (3). For both qualities $Q\in\{H,L\}$:
--
--   1. $\pi\mapsto f(\pi,Q)$ is continuous on $[0,1]$;
--   2. $f(0,Q)=0$ and $f(1,Q)=1$;
--   3. for every $\pi\in(0,1)$, $$f(\pi,L)<\pi<f(\pi,H);$$
--   4. $f(\pi,Q)>0$ for $\pi\in(0,1]$;
--   5. $f(\pi,Q)<1$ for $\pi\in[0,1)$.
--
--   The e-companion uses $f(\pi,H)>\pi$, $f(0,H)=0$ and $f(1,H)=1$ in the proofs of Theorems 1 and 2; the remaining facts are what the omitted symmetric case $q=L$ and the strict bias (EC.6) require.
--
--   Differences from the source:
--   - generalization: f(π,H) > π on (0,1), f(0,H) = 0, f(1,H) = 1 → also the q = L twins, continuity on [0,1], 0 < f on (0,1] and f < 1 on [0,1); reason: the extra clauses are facts the symmetric case and (EC.6) use; the printed facts are clauses 2–3
--   - reading: α > 0.5 → 1/2 < α < 1; reason: 'noisily reveals' (p. 11); at α = 1 clauses 1, 4, 5 fail and Theorem 2 fails (paper.md item 3)
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, e-companion, proof of Theorem 1, (EC.5)(a) and Cases (i)–(iii), proof of Theorem 2, p. ec2 (PDF 34)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

namespace PolarizedLearning

/-- **Properties of the expected posterior used in the proofs of Theorems 1–2**, Kadiyala–Shin,
*Social Learning and Content Quality under Polarization*, MSOM (2024), doi:10.1287/msom.2022.0533,
e-companion, proof of Theorem 1, (EC.5)(a) and Cases (i)–(iii), and proof of Theorem 2, p. ec2
(PDF 34): "`f(π,H) > π` for any `π ∈ (0,1)`", "`f(0,H) = 0`", "`f(1,H) = 1`".

For a signal accuracy `1/2 < α < 1` and both qualities `Q`:
1. `π ↦ f(π, Q)` is continuous on `[0,1]`;
2. `f(0, Q) = 0` and `f(1, Q) = 1`;
3. `f(π, L) < π < f(π, H)` for `π ∈ (0,1)`;
4. `0 < f(π, Q)` for `π ∈ (0,1]`;
5. `f(π, Q) < 1` for `π ∈ [0,1)`. -/
theorem expectedPosterior_props (al : ℝ) (hal_lo : 1 / 2 < al) (hal_hi : al < 1) :
    (∀ Q : Quality, ContinuousOn (fun π => f al π Q) (Set.Icc 0 1)) ∧
    (∀ Q : Quality, f al 0 Q = 0 ∧ f al 1 Q = 1) ∧
    (∀ π ∈ Set.Ioo (0 : ℝ) 1, f al π .low < π ∧ π < f al π .high) ∧
    (∀ Q : Quality, ∀ π ∈ Set.Ioc (0 : ℝ) 1, 0 < f al π Q) ∧
    (∀ Q : Quality, ∀ π ∈ Set.Ico (0 : ℝ) 1, f al π Q < 1) := by sorry

end PolarizedLearning
