-- Prove2me | Theorems.Thm_TucciCIT_appC_repeated_index_entropy
-- name    : TucciCIT.appC_repeated_index_entropy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:36.825983+00:00
-- url     : https://prove2.me/theorems/25bd172f-e939-44cf-8ffb-658ee52f98bf
-- title:
--   Appendix C — $S(R) = S(\rho)$ for repeated index pairs
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H_a$ with basis $S_a$, and let nodes $a$ and $b$ have the same set of states ($S_b = S_a$). Define the matrix with repeated index pairs
--
--   $$
--   R = \sum_{a,a'} \rho_{a,a'}\, |a = a, b = a\rangle\langle a = a', b = a'| ,
--   $$
--
--   that is, $R_{(a,b),(a',b')} = \rho_{a a'}$ if $a = b$ and $a' = b'$, and $0$ otherwise. Then
--
--   $$
--   S(R) = S(\rho).
--   $$
--
--   The paper uses this to evaluate entropies of reduced density matrices of the meta state, which repeat index pairs; in this mission it identifies one term of the strong-subadditivity argument for (4.15) with $E_F(\psi)$.
--
--   **Formalization Note** The paper calls both $R$ and $\rho$ density matrices; $R$ is one exactly when $\rho$ is, so the hypothesis is stated on $\rho$.
--
--   Differences from the source:
--   - encoding: R a density matrix (and ρ the smaller density matrix) → IsDensityMatrix ρ; reason: R is a density matrix if and only if ρ is
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, Appendix C, eqs. (C.1)–(C.2), p.31

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, Appendix C, eqs. (C.1)–(C.2), p.31 (PDF p.31): for
"R = Σa,a′ Ra,a′|a = a, b = a⟩⟨a = a′, b = a′|, where the nodes a and b have the same states
(Sa = Sb)", and "the smaller density matrix ρ = Σa,a′ Ra,a′|a⟩⟨a′|. Next we will show that
S(R) = S(ρ)."

Let `ρ` be a density matrix on `H_a` (basis `S_a`), and let `R` be the matrix on `H_a ⊗ H_b`
(`S_b = S_a`) with `R_{(a,b),(a',b')} = ρ_{a a'}` if `a = b` and `a' = b'`, and `0` otherwise
(repeated index pairs). Then `S(R) = S(ρ)` (von Neumann entropies in bits).

**Formalization Note.** The paper calls both `R` and `ρ` density matrices; `R` is one exactly
when `ρ` is, so the hypothesis is put on `ρ`. -/
theorem appC_repeated_index_entropy {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    vnEntropy (Matrix.of fun i j : A × A => if i.1 = i.2 ∧ j.1 = j.2 then ρ i.1 j.1 else 0) =
      vnEntropy ρ := by sorry

end TucciCIT
