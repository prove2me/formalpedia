-- Prove2me | Theorems.Thm_ShorWiki_phaseEstimation_eigState
-- name    : ShorWiki.phaseEstimation_eigState
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T03:04:35.99316+00:00
-- url     : https://prove2.me/theorems/d0c7be1e-adea-42ee-8703-960b1ce814bb
-- title:
--   Phase estimation on $|0\rangle^{\otimes 2n}|\psi_j\rangle$: output $|\phi_j\rangle|\psi_j\rangle$ with $p_k \ge 4/\pi^2$ at the optimal $k$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, $r = \operatorname{ord}_N(a)$, $n = \lceil\log_2 N\rceil$, and $0 \le j < r$. Apply the phase estimation circuit for the modular-multiplication gate, with a $2n$-qubit first register, to $|0\rangle^{\otimes 2n}|\psi_j\rangle$. Then there is a state $|\phi_j\rangle$ of the first register such that:
--
--   1. the output is the product state $|\phi_j\rangle|\psi_j\rangle$;
--   2. for every $k \in \{0,\dots,2^{2n}-1\}$ with $\left|\frac{k}{2^{2n}} - \frac{j}{r}\right| \le \frac{1}{2^{2n+1}}$ (a nearest integer to $2^{2n}j/r$),
--   $$p_k = |\langle k|\phi_j\rangle|^2 \ge \frac{4}{\pi^2}.$$
--
--   This is the guarantee of quantum phase estimation specialised to the eigenstates of $U$.
--
--   **Formalization Note** The article writes $p_{2^{2n}j/r}$, which is meaningful only when $2^{2n}j/r$ is an integer; it is formalized as the probability of any nearest integer $k$ to $2^{2n}j/r$, the "optimal bitstring" of the section *Choosing the size of the first register*.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF p. 5)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem phaseEstimation_eigState (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) (hj : j < ord N a) :
    ∃ φ : Fin (2 ^ (2 * regBits N)) → ℂ,
      phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
          tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j)
        = tensorState φ (eigState N a (regBits N) j) ∧
      ∀ k : Fin (2 ^ (2 * regBits N)),
        |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
            ≤ 1 / 2 ^ (2 * regBits N + 1) →
          4 / Real.pi ^ 2 ≤ ‖φ k‖ ^ 2 := by sorry

end ShorWiki
