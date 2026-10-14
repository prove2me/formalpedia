-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_ampEncoding_gateComplexity
-- name    : QAlgorithms.Nannicini.ampEncoding_gateComplexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:46:31.097368+00:00
-- url     : https://prove2.me/theorems/fbabaf63-c2a0-47ce-b66b-26a4f3805cdd
-- title:
--   Amplitude encoding of a complex vector to error ϵ with Õ(d) gates from {H, T, CX}
-- statement:
--   For a nonzero vector $x \in \mathbb{C}^d$ let $n = \lceil \log_2 d \rceil$ and
--
--   $$
--   |\mathrm{amp}(x)\rangle = \sum_{j=0}^{d-1} \frac{x_j}{\|x\|} |\vec\jmath\rangle
--   $$
--
--   be its amplitude encoding on $n$ qubits, where $\vec\jmath$ is the $n$-bit binary expansion of $j$ (most significant bit first) and the basis states with $j \ge d$ have amplitude $0$. Circuits are built from the universal gate set $\{H, T, CX\}$, and their size is their number of gates.
--
--   There are constants $C > 0$ and $c \in \mathbb{N}$ such that for every $d \ge 1$, every nonzero $x \in \mathbb{C}^d$ and every $\epsilon > 0$ there exist a number $w$ of ancilla qubits and a circuit $Q$ on $n + w$ qubits with
--
--   $$
--   |Q| \le C\, d\, \bigl(\log(2+d) + \log(2 + 1/\epsilon)\bigr)^{c}
--   \quad\text{and}\quad
--   \bigl\| Q |0^{n+w}\rangle - |\mathrm{amp}(x)\rangle \otimes |0^w\rangle \bigr\| \le \epsilon .
--   $$
--
--   The circuit may depend on $x$ (it is produced from the classical description of $x$); the constants do not depend on $d$, $x$ or $\epsilon$. This is the gate cost of loading a classical vector into the amplitudes of a quantum state in the standard circuit model, against which the QRAM speedup of §5.3 is measured.
--
--   **Formalization Note** $\tilde O(d)$ with polylogarithmic dependence on $1/\epsilon$ (as the source's proof says) is written as $C d$ times a power of $\log(2+d) + \log(2+1/\epsilon)$. The error is the Euclidean distance of the produced state from $|\mathrm{amp}(x)\rangle$ with the ancillas back in $|0\rangle$. The statement covers every nonzero $x \in \mathbb{C}^d$, which includes every finite-precision description.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 126, Corollary 5.37. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.126, Corollary 5.37: "Given a classical description of `x ∈ ℂ^d` in finite
precision, there is a circuit that implements the mapping `|0⟩ → |amp(x)⟩` with error at most
`ϵ` with gate complexity `Õ(d)`."

The circuit is built from the classical data `x` (Rem. 5.35), over the gate set `{H, T, CX}` of
Thm. 1.43, on the `n = ⌈log d⌉` qubits of `|amp(x)⟩` plus `w` ancillas that start in `|0⟩`.
"Error at most `ϵ`" is the Euclidean distance between the produced state and
`|amp(x)⟩ ⊗ |0^w⟩` (§1.3.6). `Õ(d)` with the dependence on `ϵ` polylogarithmic (p.127) is
`C · d · (log(2 + d) + log(2 + 1/ϵ))^c` with constants `C > 0`, `c` chosen before `d`, `x`, `ϵ`.
The statement is for every nonzero `x ∈ ℂ^d`, which contains every finite-precision input. -/
theorem ampEncoding_gateComplexity :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) (x : Fin d → ℂ), x ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ (w : ℕ) (circ : Circuit htcxGateSet (Nat.clog 2 d + w)),
        (circ.size : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        ‖act circ.unitary (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  sorry











end QAlgorithms.Nannicini
