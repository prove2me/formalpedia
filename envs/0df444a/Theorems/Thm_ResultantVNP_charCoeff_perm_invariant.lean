-- Prove2me | Theorems.Thm_ResultantVNP_charCoeff_perm_invariant
-- name    : ResultantVNP.charCoeff_perm_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:28.904794+00:00
-- url     : https://prove2.me/theorems/8db9e1ee-1953-4f79-b0d4-e679fd1e9e24
-- title:
--   Section 3.1 — $\Phi_{n,s}$ is invariant under relabelling the indices
-- statement:
--   For every $n$, every $s\in\mathbb N$ and every permutation $\pi\in S_n$, relabelling the indices of the symmetric tensor by $\pi$, i.e. substituting $a_{\{i,j,k\}}\mapsto a_{\{\pi(i),\pi(j),\pi(k)\}}$, leaves $\Phi_{n,s}$ unchanged.
--
--   The paper derives this from the invariance of $\mathrm{Det}_n$ (Lemma 2.8), which must hold in each homogeneous component. It is the invariance used in the proof of Theorem 3.5.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, invariance of Φ_{n,s} (after Definition 3.1), p.14

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff

namespace ResultantVNP

/-- **Invariance of `Φ_{n,s}` under relabelling.** `Det_n` is invariant under relabelling the indices by
a permutation `π ∈ S_n`; because the invariance must hold in each homogeneous component, it also
applies to `Φ_{n,s}` for all `s ∈ ℕ`: the substitution `a_{{i,j,k}} ↦ a_{{π(i),π(j),π(k)}}` leaves
`Φ_{n,s}` unchanged.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, invariance of Φ_{n,s}, p.14 (the two sentences after Definition 3.1).

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. Stated for every `n` (for `n = 0` it is trivial). -/
theorem charCoeff_perm_invariant (𝓡 : ResultantSystem) (n s : ℕ) (π : Equiv.Perm (Fin n)) :
    MvPolynomial.rename (Sym.map π) (charCoeff 𝓡 n s) = charCoeff 𝓡 n s := by sorry

end ResultantVNP
