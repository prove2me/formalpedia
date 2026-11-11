-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_correctness
-- name    : PauliUnclonable531.Pauli.correctness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:09.141444+00:00
-- url     : https://prove2.me/theorems/4cddb500-9010-4fff-a59d-c103c6d45a90
-- title:
--   Lemma 3.1 — perfect correctness
-- statement:
--   For every n≥1, supported key k, message m and decryption outcome m′, the scheme's exact outcome law is
--
--   $$\operatorname{Tr}[Q_{k,m'}\rho_{k,m}]=\mathbf 1[m'=m].$$
--
--   Here ρ is the Section 3 ciphertext and Q is the Section 3 decryption effect. In particular decryption returns the original bit with probability one for each supported key, rather than merely on average over keys. The full binary law is the displayed computation on p.16.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Lemma 3.1, p.15, with its outcome-law computation on p.16

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Scheme

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Lemma 3.1 and its displayed outcome law, pp.15–16. -/
theorem correctness (n : ℕ) (hn : 1 ≤ n) (k : Key n) (m m' : Fin 2) :
    born (decryptEffect k m') (ciphertext k m) = if m' = m then 1 else 0 := by sorry

end PauliUnclonable531.Pauli
