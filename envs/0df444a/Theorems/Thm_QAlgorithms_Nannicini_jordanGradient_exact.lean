-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_jordanGradient_exact
-- name    : QAlgorithms.Nannicini.jordanGradient_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:46:30.254594+00:00
-- url     : https://prove2.me/theorems/7ac6c401-2eab-46a0-853a-ef6d4bd775b8
-- title:
--   Jordan's gradient circuit recovers the gradient of an exactly representable linear function
-- statement:
--   This is Jordan's quantum gradient algorithm in its exact form.
--
--   Fix integers $d \ge 0$ and $q \ge 0$. Work with $d+1$ registers of $q$ qubits each, a $q$-bit string being read as an integer $0, \dots, 2^q-1$ (most significant bit first). The binary oracle of Definition 5.1 is
--
--   $$
--   U_f\,|x_1\rangle\cdots|x_d\rangle|y\rangle = |x_1\rangle\cdots|x_d\rangle|y \boxplus f(x_1,\dots,x_d)\rangle,
--   $$
--
--   where $\boxplus$ is addition modulo $2^q$. Assume $f$ is linear, $f(x) = \langle g, x\rangle + b$, where each gradient component $g_i \in \{0,\dots,2^q-1\}$ is exactly representable on $q$ bits and $b$ is a nonnegative integer. The circuit of Fig. 5.1 starts in $|0\rangle^{\otimes d}\otimes|1\cdots1\rangle$, applies $H^{\otimes q}$ to each of the first $d$ registers and the quantum Fourier transform $Q_q$ to the last one, applies $U_f$ once, and then applies $Q_q^\dagger$ to each of the first $d$ registers. Then measuring the first $d$ registers gives the gradient with certainty:
--
--   $$
--   \Pr\big[(\text{first } d \text{ registers}) = (g_1,\dots,g_d)\big] = 1.
--   $$
--
--   This is the multidimensional phase-estimation principle behind every later gradient algorithm in the chapter: one oracle call gives all $d$ components at once, where classical finite differences need $d+1$ evaluations.
--
--   **Formalization Note** The circuit is the fixed definition `jordanGradientState`, which contains exactly one application of $U_f$. The function value enters the register modulo $2^q$, as $\boxplus$ prescribes. The source's assumption that $f(x)$ itself is representable on $q$ bits is not imposed: imposing it for all grid points would force almost all $g_i$ to be $0$. The theorem holds without it.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 108, Proposition 5.3. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.108, Proposition 5.3 (Jordan's gradient algorithm, exactly linear case). Let
`U_f |x_1⟩⋯|x_d⟩|y⟩ = |x_1⟩⋯|x_d⟩|y ⊞ f(x_1, …, x_d)⟩` be the binary oracle of Def. 5.1 (p.106),
every register on `q` qubits, `⊞` addition modulo `2^q`. Assume `f` is linear,
`f(x) = ⟨g, x⟩ + b`, where `x = (x_1, …, x_d)` are the integers written in the `d` input
registers (Eq. (5.1)), and that every component `g_i` of the gradient is exactly representable on
`q` bits (`g_i` is the integer of a `q`-bit string) and `b` is a nonnegative integer (so that
`f(x)` is an integer; it enters the register modulo `2^q`). Then the circuit of Fig. 5.1 (start
in `|0⟩^{⊗d} ⊗ |1⃗⟩`, apply `H^{⊗q}` to the first `d` registers and `Q_q` to the last, one
application of `U_f`, then `Q_q†` on each of the first `d` registers) yields the gradient: the
measurement of the first `d` registers returns `(g_1, …, g_d)` with probability `1`. The single
application of `U_f` is structural in `jordanGradientState`. -/
theorem jordanGradient_exact (d q : ℕ) (g : Fin d → Qubits q) (b : ℕ) :
    let F : (Fin d → Qubits q) → ℕ := fun x => ∑ i, bitsToNat (g i) * bitsToNat (x i) + b
    marginalFst (jordanGradientState d q F) g = 1 := by
  sorry







end QAlgorithms.Nannicini
