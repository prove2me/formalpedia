-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_45
-- name    : SpencerEight.lemma_8_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:18.003601+00:00
-- url     : https://prove2.me/theorems/c01808e5-17a9-4386-b6ee-98f5df0995ab
-- title:
--   Lemma 8.45 — completing a finite schedule
-- statement:
--   Start from symmetric contractions. Suppose $r$ partial signings $M_i$ satisfy $\|M_i\|\le L_i\sqrt n$, where $L_i>0$ and $C_i:=C_0-\sum_{h=1}^iL_h>0$. After step $i$, replace every remaining coefficient matrix $B$ by
--   $$C_i\sqrt nH_i^{-1/2}BH_i^{-1/2},\qquad H_i:=C_{i-1}\sqrt nI-|M_i|.$$
--   Suppose the final active fraction is at most $v_0$. Suppose $s$ subsequent phases satisfy Lemma 8.43 with $(w,L,q,b):=(v_{k-1},c_k,q_k,0)$, and put $v_k:=q_kv_{k-1}$. If $0<v_s<e^{-731/256}$ and
--   $$\mathcal B:=\sum_{i=1}^rL_i+\sum_{k=1}^sc_k+\mathcal T_{s_+}(v_s)<C_0,$$
--   the original family has a complete signing of norm at most $\mathcal B\sqrt n$.
--
--   The schedule data of the goal theorem are applied through this lemma.
--
--   Differences from the source:
--   - reading: s subsequent phases satisfy Lemma 8.43 with (w, L, q, b) := (v_{k−1}, c_k, q_k, 0) → SuffixPhase: a_k, β_k ≥ 0, η_k > 0, the radius and reserve conditions, and the mass of the norm body for every nonempty subfamily of the final active set of size at most v_{k−1}n; reason: this is what the proof feeds to Lemma 8.43; the page does not list these numbers separately
--   - encoding: partial signings M_i and replaced coefficients → PrefixRun: active sets, y_i ∈ {−1, 0, 1} and the level families, with steps numbered from 0; reason: the equations determine these objects from A, y, L as on the page
--   - encoding: n the dimension, with √n in the replacement → 0 < n; reason: a nondegeneracy condition
--   - encoding: the scalar B → the sum written out in the hypothesis and in the conclusion; reason: the page overloads the letter B
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.45, p.106 (PDF p.106)

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_sPlus
import Definitions.Def_SpencerEight_tailCost
import Definitions.Def_SpencerEight_PrefixRun
import Definitions.Def_SpencerEight_SuffixPhase
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- Lemma 8.45 (Completing a finite schedule), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.106 (PDF p.106). The prefix is `PrefixRun`; the suffix phases, with `v_k := q_k v_{k−1}`, are `SuffixPhase` on the family after the last prefix step. `B` on the page is the scalar written out in the conclusion and in `hB`.

**Formalization Note** The phrase "`s` subsequent phases satisfy Lemma 8.43" is read as in `SuffixPhase`. The size of the original family is not constrained: the proof uses only the final fraction `|S_r| ≤ v₀n`. -/
theorem lemma_8_45 {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, IsSymmContraction (A i)) (C0 : ℝ) (r : ℕ)
    (L : ℕ → ℝ) (S : ℕ → Finset ι) (y : ℕ → ι → ℝ) (Bk : ℕ → ι → Matrix (Fin n) (Fin n) ℝ)
    (run : PrefixRun A C0 r L S y Bk) (s : ℕ) (v c q : ℕ → ℝ)
    (hv0 : ((S r).card : ℝ) ≤ v 0 * n) (hv : ∀ k < s, v (k + 1) = q (k + 1) * v k)
    (hphase : ∀ k < s, SuffixPhase (Bk r) (S r) (v k) (c (k + 1)) (q (k + 1)))
    (hvs0 : 0 < v s) (hvs : v s < Real.exp (-(731 / 256)))
    (hB : ∑ i ∈ Finset.Icc 1 r, L i + ∑ k ∈ Finset.Icc 1 s, c k + tailCost sPlus (v s) < C0) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ‖signedSum A ε‖ ≤
        (∑ i ∈ Finset.Icc 1 r, L i + ∑ k ∈ Finset.Icc 1 s, c k + tailCost sPlus (v s)) *
          Real.sqrt n := by sorry

end SpencerEight
