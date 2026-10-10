-- Prove2me | Theorems.Thm_SubSuperStoch_SubSpec_eigenvalue_pow_le_normInf
-- name    : SubSuperStoch.SubSpec.eigenvalue_pow_le_normInf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:31.810874+00:00
-- url     : https://prove2.me/theorems/4225de3d-8898-41fa-b207-25b996940f76
-- title:
--   Proof of Theorem 2.2, p. 5 — the known facts ρ(A^m) = ρ^m(A) ≤ ‖A^m‖_∞, in eigenvalue form
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ and let $m$ be a natural number. Every complex eigenvalue $\mu$ of $A$ satisfies
--   $$|\mu|^m\le\|A^m\|_\infty .$$
--   Equivalently, $\rho(A)^m=\rho(A^m)\le\|A^m\|_\infty$, the two "known facts" invoked at the end of the proof of Theorem 2.2.
--
--   This converts the norm bound on $F^{|\mathcal C^*|+1}$ into the spectral radius bound (2.1).
--
--   **Formalization Note** The spectral radius is not a separate object: the statement quantifies over the complex spectrum `specC A`. For $m=0$ both sides equal $1$ when $n\ge 1$, and the spectrum is empty when $n=0$, so no restriction on $m$ is needed.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 5, proof of Theorem 2.2 (last sentence: "the known facts ρ(F^{|C*|+1}) = ρ^{|C*|+1}(F) and ρ(F^{|C*|+1}) ≤ ‖F^{|C*|+1}‖_∞")

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SubSpec

theorem eigenvalue_pow_le_normInf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    ∀ μ ∈ specC A, ‖μ‖ ^ m ≤ normInf (A ^ m) := by sorry

end SubSuperStoch.SubSpec
