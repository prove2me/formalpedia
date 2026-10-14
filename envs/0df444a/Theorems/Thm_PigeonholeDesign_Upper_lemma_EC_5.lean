-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_lemma_EC_5
-- name    : PigeonholeDesign.Upper.lemma_EC_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:03.055825+00:00
-- url     : https://prove2.me/theorems/d86821dc-7fe9-46ac-b3ca-adb1da655b1e
-- title:
--   Lemma EC.5 — ALG^C is invariant under permutations of the arrival sequence
-- statement:
--   Let $x',x''\in\mathbb R^T$ be two arrival sequences and $\sigma:[T]\to[T]$ a bijection with $x'_t=x''_{\sigma(t)}$ for every $t\in[T]$. Then the completely randomized design has the same expected discrepancy on both sequences:
--   $$\mathrm{ALG}^{\mathsf C}(x')=\mathrm{ALG}^{\mathsf C}(x'').$$
--
--   The completely randomized design ignores arrival order, so its performance depends only on the multiset of covariates. This reduces the worst case of Lemma 2 to sorted instances.
--
--   **Formalization Note** The sequences are functions on `Fin T` and $x'=x''\circ\sigma$. No range restriction on the covariates is needed.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec4 (PDF p. 42), Lemma EC.5

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem lemma_EC_5 {T : ℕ} (σ : Equiv.Perm (Fin T)) (x : Fin T → ℝ) :
    crdExp (x ∘ σ) = crdExp x := by sorry

end PigeonholeDesign.Upper
