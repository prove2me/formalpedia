-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_quantumGV_nondegenerate_exists
-- name    : QAlgorithms.GottesmanIntro.quantumGV_nondegenerate_exists
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T19:50:00.483026+00:00
-- url     : https://prove2.me/theorems/f59b5824-1b41-4deb-9136-7a1d2df66cd1
-- title:
--   Finite nondegenerate quantum Gilbert–Varshamov existence bound
-- statement:
--   This theorem states the nondegenerate form of the finite quantum Gilbert–Varshamov existence bound.
--
--   Let $n, k, d \in \mathbb{N}$ with $d \ge 1$. If
--
--   $$
--   \left(\sum_{j=0}^{d-1} 3^j \binom{n}{j}\right) 2^k \le 2^n,
--   $$
--
--   then there exists a subspace $C \subseteq (\mathbb{C}^2)^{\otimes n}$ of dimension $2^k$ that is an $[[n,k,d]]$ quantum error-correcting code and is nondegenerate at weight $t = \lfloor (d-1)/2 \rfloor$.
--
--   In Gottesman's proof of the quantum Gilbert–Varshamov bound (Theorem 4, eq. (36)), the iteratively constructed code satisfies $\langle\psi_i|E|\psi_i\rangle = 0$ for every non-identity Pauli error $E$ of weight less than $d$, so the resulting code is pure (and hence nondegenerate at $\lfloor (d-1)/2 \rfloor$), which is used directly in establishing the asymptotic nondegenerate rate window of equation (37).
--
--   **Formalization Note** Nondegeneracy at $t = \lfloor(d-1)/2\rfloor$ is expressed by `IsNondegenerate C ((d - 1) / 2)` along with `IsQCode n k d C`.
-- source:
--   D. Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, https://arxiv.org/abs/0904.2557v1, pp.7–8, Theorem 4, equations (36)–(37)

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

namespace QAlgorithms.GottesmanIntro
theorem quantumGV_nondegenerate_exists :
    ∀ n k d : ℕ, 1 ≤ d →
      (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n →
      ∃ C : Submodule ℂ (EuclideanSpace ℂ (Qubits n)),
        IsQCode n k d C ∧ IsNondegenerate C ((d - 1) / 2) := by sorry
end QAlgorithms.GottesmanIntro
