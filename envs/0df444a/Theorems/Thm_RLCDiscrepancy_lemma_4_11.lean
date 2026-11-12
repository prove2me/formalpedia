-- Prove2me | Theorems.Thm_RLCDiscrepancy_lemma_4_11
-- name    : RLCDiscrepancy.lemma_4_11
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:53:24.494272+00:00
-- url     : https://prove2.me/theorems/e2497713-9a74-4c07-9c90-6c0c7ecab347
-- title:
--   Lemma 4.11 — translation invariance of $F_f$
-- statement:
--   For every function $f:\mathbb F_q^n\to\mathbb R$ and every $z\in\mathbb F_q^n$, the translation $f_z(x)=f(x+z)$ has the same self-convolution as $f$:
--
--   $$
--   F_{f_z}=F_f .
--   $$
--
--   This is why a single smoothness event for $F_f$ serves all $q^n$ translates of $f$ at once in the proof of Theorem 2.4.
--
--   Differences from the source:
--   - encoding: F_q and F^n_q → a finite field `F` with q = `Fintype.card F`, and `Fin n → F`; reason: every prime power is the size of a finite field; same instances
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.11, p.29

import Mathlib
import Definitions.Def_RLCDiscrepancy_transl
import Definitions.Def_RLCDiscrepancy_selfConv

namespace RLCDiscrepancy

/-- **Lemma 4.11** (translation invariance of F_f). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Lemma 4.11, p.29: "For any function
f : F^n_q → R and any translation vector z ∈ F^n_q, let f_z be its translation. Then
F_{f_z} = F_f." -/
theorem lemma_4_11 {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ)
    (z : Fin n → F) : selfConv (transl f z) = selfConv f := by sorry

end RLCDiscrepancy
