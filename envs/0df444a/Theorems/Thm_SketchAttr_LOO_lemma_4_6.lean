-- Prove2me | Theorems.Thm_SketchAttr_LOO_lemma_4_6
-- name    : SketchAttr.LOO.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:32.805808+00:00
-- url     : https://prove2.me/theorems/114b7da6-814b-4927-ad8f-4cd495b426ec
-- title:
--   Lemma 4.6 — Taylor truncation
-- statement:
--   Let $f:\mathbb C^n\to\mathbb C$ be an $\alpha$-stable arithmetic circuit. For every nonzero $w\in\mathbb C^n$ such that $\alpha(4\|w\|_2)<\infty$ and every integer $N\ge1$,
--   $$\left|f(w)-\sum_{r=0}^N T_f^{(r)}[w^{\otimes r}]\right|\le\frac{4^{-N}}3\alpha(4\|w\|_2).$$
--   The result bounds the discarded Taylor degrees at arbitrary complex inputs. Arithmetic circuits are the standing domain of stability in Definition 4.5, so no extra smoothness or coefficient hypothesis is needed.
--
--   Differences from the source:
--   - encoding: complex vectors and a finite value of the extended nonnegative stability profile → Euclidean complex coordinates, an explicit nonzero vector, and toReal only under a finiteness hypothesis; reason: the Euclidean norm and absolute value agree with the source and infinity cannot silently become zero
--   - encoding: positive integer input dimension n and indices in [n] → Fin n with an explicit hypothesis 1 <= n; reason: this records the positive-dimension convention in Section 3.1 and changes only the index base
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 13, Lemma 4.6, using Definition 4.5 on p. 12; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Stability
open scoped ENNReal

namespace SketchAttr.LOO

/-- Lemma 4.6 is stated for circuit functions, the standing domain of Definition 4.5. -/
theorem lemma_4_6 (n : ℕ) (hn : 1 ≤ n) (c : Circuit n 1) (α : StabilityProfile)
    (hstable : IsStable (circuitFunction c) α) (w : Vec n) (hw : w ≠ 0)
    (hfinite : α ⟨4*‖w‖, mul_pos (by norm_num) (norm_pos_iff.mpr hw)⟩ < ⊤)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖circuitFunction c w - ∑ r ∈ Finset.range (N+1),
      diagonal (taylorTensor (circuitFunction c) r) w‖ ≤
      (4 : ℝ)^(-(N : ℤ))/3 *
        (α ⟨4*‖w‖, mul_pos (by norm_num) (norm_pos_iff.mpr hw)⟩).toReal := by sorry

end SketchAttr.LOO
