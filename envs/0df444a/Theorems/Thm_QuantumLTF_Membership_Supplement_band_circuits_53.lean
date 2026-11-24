-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_band_circuits_53
-- name    : QuantumLTF.Membership.Supplement.band_circuits_53
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-24T08:01:22.067212+00:00
-- url     : https://prove2.me/theorems/f8cb49bb-d53d-4b39-a82f-5b201954050e
-- title:
--   Reversible degree-band marker, reflection, and first-hit swap circuits for Theorem 5.3
-- statement:
--   We establish the existence of an explicit elementary reversible circuit suite over the universal $1$- and $2$-qubit gate set realizing the degree-band predicates, reflections, and parallel block-routing permutations required by Theorem 5.3.
--
--   There exists a universal constant $C_{\mathrm{circ}} > 0$ such that for all parameters $n, K, D, q, a \in \mathbb{N}$ (representing dimension $n$, band parameter $K$, degree cutoff $D$, coordinate bit-width $q$, and $a$ internal ancillas), there exist clean-ancilla circuits over the elementary gate set with the following guarantees (every ancilla starts and ends in $|0\rangle$ on all computational basis inputs):
--
--   1. **Good-band marker.** On $(nq + 1 + a)$ system wires, $1$ target bit $b \in \{0,1\}$, and clean ancillas, a circuit of at most
--   $$
--   C_{\mathrm{circ}}\bigl(n(q + \lceil \log_2(nD + 2) \rceil + 1) + a + 1\bigr)
--   $$
--   gates maps computational basis state $|z\rangle |b\rangle |0\rangle$ to $|z\rangle |b \oplus g(z)\rangle |0\rangle$, where $g(z) \in \{0,1\}$ indicates whether $z = (x, y, s)$ satisfies $y = 1$, $s = 0^a$, $\alpha_i < D$ for all $0 \le i < n$, and $K \le \sum_{i=0}^{n-1} \alpha_i \le 2K$.
--
--   2. **Good-band reflection.** Within the same gate-count bound, a clean-ancilla circuit on $nq + 1 + a$ system wires implements the reflection $|z\rangle |0\rangle \mapsto (-1)^{g(z)} |z\rangle |0\rangle$.
--
--   3. **Zero-state reflection.** A clean-ancilla circuit on $nq + 1 + a$ system wires of at most $C_{\mathrm{circ}}(nq + a + 1)$ gates implements $|z\rangle |0\rangle \mapsto (-1)^{\mathbf{1}[z = 0]} |z\rangle |0\rangle$.
--
--   4. **First-hit block swap.** For any $R, m_{\mathrm{reg}} \in \mathbb{N}$, a clean-ancilla circuit of at most $C_{\mathrm{circ}} R (m_{\mathrm{reg}} + 1)$ gates acting on $R$ register blocks $(B_0, \dots, B_{R-1}) \in (\{0,1\}^{m_{\mathrm{reg}}})^R$ and read-only flag bits $f \in \{0,1\}^R$ swaps block $0$ with block $j^*(f) = \min\{j < R : f_j = 1\}$ whenever $f \neq 0^R$, and leaves all blocks unchanged when $f = 0^R$.
--
--   This theorem encapsulates all explicit `gates12` circuit constructions and gate-count bounds for Theorem 5.3, allowing the top-level amplitude-amplification proof to treat the arithmetic checking, reflection, and routing primitives modularly.
--
--   **Formalization Note.** The statement asserts `Nonempty BandCircuits53`, where `BandCircuits53` is defined in `QuantumLTF_Membership_Supplement_goodBasis53` together with the MSB-first predicate `isGoodBasis53` and block permutation `swappedBlocks53`.
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §5.2, Theorem 5.3, pp. 63–65

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_goodBasis53

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

theorem band_circuits_53 : Nonempty BandCircuits53 := by sorry

end QuantumLTF.Membership.Supplement
