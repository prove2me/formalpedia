-- Prove2me | Theorems.Thm_QLocalCert_quantum_fingerprints
-- name    : QLocalCert.quantum_fingerprints
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:31.029198+00:00
-- url     : https://prove2.me/theorems/e65645a6-61ed-4cd5-b6ec-ed9328bb2d93
-- title:
--   Quantum fingerprints [BCWDW01]: $O(\log N)$ qubits with $|\langle h_X|h_Y\rangle|^2\le 1/2$
-- statement:
--   There is a constant $C$ such that for every $N\ge2$ there exist $\ell\le C\log_2N$ and an assignment of a unit vector $|h_X\rangle\in\mathbb C^{2^\ell}$ (an $\ell$-qubit pure state) to every string $X\in\{0,1\}^N$ with
--   $$
--   |\langle h_X|h_Y\rangle|^2\le\tfrac12\qquad\text{whenever }X\ne Y .
--   $$
--
--   These are the quantum fingerprints of Buhrman, Cleve, Watrous and de Wolf, used by the paper as stated in §2, p.15 ("Its precise construction is not needed here"). They are the states compared along the central path in Protocol 1.
--
--   Differences from the source:
--   - encoding: |h_X⟩ has O(log N) qubits → ∃ C, ∀ N ≥ 2, ∃ ℓ ≤ C log₂ N; reason: big-O as one constant chosen before N; N ≥ 2 because log₂ 1 = 0 and two distinct strings need dimension at least 2
--   - encoding: quantum fingerprint |h_X⟩ → unit vector Qb ℓ → ℂ with star h ⬝ᵥ h = 1, existence of the family; reason: the paper uses only the size and the overlap bound
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §2, p.15 (citing Buhrman, Cleve, Watrous, de Wolf, Quantum fingerprinting, Phys. Rev. Lett. 87, 167902, 2001)

import Mathlib
import Definitions.Def_QLocalCert_piKron

open Matrix
set_option autoImplicit false

namespace QLocalCert

/-- **Quantum fingerprints** [BCWDW01], as used in §2, p.15: "For an N-bit string X, a quantum
fingerprint |h_X⟩ has O(log N) qubits and satisfies |⟨h_X|h_Y⟩|² ≤ 1/2 whenever X ≠ Y."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §2, p.15, citing Buhrman, Cleve, Watrous, de Wolf, *Quantum fingerprinting* (2001).

**Formalization Note.** `O(log N)` is one constant `C` before `N`, for every `N ≥ 2`
(`log₂ N > 0`). A fingerprint family is a map `h` from `{0,1}^N` to unit vectors of
`ℂ^{2^ℓ}` (`Qb ℓ → ℂ`); `star u ⬝ᵥ v = ⟨u|v⟩`. Existence of the family is the content used by the
paper ("Its precise construction is not needed here"). -/
theorem quantum_fingerprints :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∃ ℓ : ℕ, (ℓ : ℝ) ≤ C * Real.logb 2 N ∧
      ∃ h : (Fin N → Bool) → Qb ℓ → ℂ, (∀ X, star (h X) ⬝ᵥ h X = 1) ∧
        ∀ X Y, X ≠ Y → ‖star (h X) ⬝ᵥ h Y‖ ^ 2 ≤ 1 / 2 := by sorry

end QLocalCert
