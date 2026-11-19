-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_jsqd_subset_sampling_process_limit
-- name    : StrictCompatLB.MeanField.jsqd_subset_sampling_process_limit
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:55:10.026704+00:00
-- url     : https://prove2.me/theorems/d78c44d2-1732-49d8-b996-9d9c4e1bbf17
-- title:
--   JSQ($d$) with subset sampling has the same process-level limit as JSQ($d$) with independent samples
-- statement:
--   Let $0<\lambda<1$, $d\ge 2$, and let $\{G_N\}$ be a connected, proportionally sparse graph sequence. Fix initial states $z_0(N)$, a path $s:[0,\infty)\to\mathbb{R}^{\mathbb{N}}$ and $T\ge 0$. Suppose that the load-balancing process in which each arriving task at dispatcher $w$ is routed by the Lipschitz assignment function of the JSQ($d$) policy (the $d$ servers sampled independently, i.e. with replacement, $p = $ `jsqdAssign d`) started from $z_0(N)$ satisfies, on every probability space,
--
--   $$\mathbb{P}\Big(\sup_{t\in[0,T]}\|q(\Phi(G_N,t))-s(t)\|_1\ge\varepsilon\Big)\to 0\quad(N\to\infty)\ \text{for all }\varepsilon>0.$$
--
--   Then the same convergence holds for the JSQ($d$) process of the model, in which the $d$ servers are a uniformly random subset of size $d$ of the neighbourhood $N_w$ (sampling without replacement, `jsqdRoute`), started from the same initial states.
--
--   Role: this is the step of the proof of Theorem 3.4 that transfers the process-level limit of Theorem 4.3, which is stated for Lipschitz assignment functions (JSQ($d$) with independent samples, Lemma 4.2), to the JSQ($d$) policy of the model, which samples a subset of $N_w$; the parent combines it with Theorem 4.3 and Lemma 4.2 for the process-level half of Theorem 3.4.
--
--   **Formalization Note**: the hypothesis is the conclusion of Theorem 4.3 for $p=$ `jsqdAssign d`, quantified over all probability spaces carrying an `IsLBProcess` for that routing; the occupancy paths are compared with the same $s$ in sup-$\ell^1$ distance on $[0,T]$.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Section 4.4 Proof of Theorem 3.4, p. 23 (process-level part 'follows from Theorem 4.3'), with the JSQ(d) sampling model of Section 2, p. 8-9 (subsets of N_w, cf. proof of Lemma H.2, p. 47) and the Lipschitz JSQ(d) assignment of Lemma 4.2, p. 15

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

theorem jsqd_subset_sampling_process_limit : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) → ∀ (G : (N : ℕ) → Finset (Fin N × Fin (M N))),
  IsConnectedSeq M G → IsPropSparse M G →
  ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (s : ℝ → ℕ → ℝ) (T : ℝ), 0 ≤ T →
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P lam M N (piRoute M G N (jsqdAssign d)) (z₀ N) (Y N) (τ N)) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0)) →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
      (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T}) atTop (𝓝 0) := by sorry

end StrictCompatLB.MeanField
