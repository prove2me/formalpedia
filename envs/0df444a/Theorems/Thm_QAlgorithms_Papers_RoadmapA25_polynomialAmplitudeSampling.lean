-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA25_polynomialAmplitudeSampling
-- name    : QAlgorithms.Papers.RoadmapA25.polynomialAmplitudeSampling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:36:03.20697+00:00
-- url     : https://prove2.me/theorems/c01d9c4f-16ff-4051-82d5-8dfeeadf50eb
-- title:
--   Sampling from a Pellian or semi-Pellian polynomial while retaining the signal
-- statement:
--   Let $a\in[0,1]$ be an unknown amplitude in the completed two-dimensional Grover space. Choose an orthonormal pair $|\Pi\rangle,|\Pi^\perp\rangle$, set $\bar a=\sqrt{1-a^2}$, and write $|\psi\rangle=a|\Pi\rangle+\bar a|\Pi^\perp\rangle$ and $|\psi^\perp\rangle=\bar a|\Pi\rangle-a|\Pi^\perp\rangle$. The endpoint states are understood as rays. Define $Z_\psi=|\psi\rangle\langle\psi|-|\psi^\perp\rangle\langle\psi^\perp|$ and $Z_\Pi=|\Pi\rangle\langle\Pi|-|\Pi^\perp\rangle\langle\Pi^\perp|$. A complex polynomial $P$ is Pellian if there is a polynomial $Q$ of the opposite fixed parity such that $|P(x)|^2+(1-x^2)|Q(x)|^2=1$ for every $x\in[-1,1]$. A real polynomial is semi-Pellian if it is the coefficientwise real part of a Pellian polynomial.
--
--   There is an absolute constant $C>0$ such that, for every Pellian or semi-Pellian polynomial $P$, an oracle instrument can be chosen independently of $a$ and of the orthonormal basis. Given one copy of any of the four states and its known classical label, the instrument outputs a bit $b_P$ satisfying
--
--   $$
--   \Pr[b_P=1]=|P(a)|^2.
--   $$
--
--   It also returns a classical label $L$ for a retained signal state. For each joint outcome $(b_P,L)$ of probability $p$, the unnormalized signal density matrix is exactly $p|L\rangle\langle L|$, with $L\in\{\psi,\psi^\perp,\Pi,\Pi^\perp\}$. This includes both sampled-bit outcomes. The total number of oracle calls, including the oracle-assisted final basis measurement, is at most $C(\deg P+1)$ for every input label. Pellian sampling uses arbitrary-angle rotations $e^{i\phi Z_\psi},e^{i\phi Z_\Pi}$, with the controlled measurement access used in the proof. Semi-Pellian sampling uses the distinct primitives $|0\rangle\langle0|\otimes e^{i\phi Z}+|1\rangle\langle1|\otimes e^{-i\phi Z}$ for each basis. Ancilla preparation and known ancilla gates are free in this query model.
--
--   The retained-state guarantee allows successive polynomial samples from the same signal system, without requiring that each invocation restore the original state.
--
--   **Formalization Note** The completed Grover-space model includes $a=0,1$ and uses density matrices to ignore global phase. The asymptotic query claim is expressed with a uniform additive degree-zero allowance. Controlled access for the Pellian basis measurement is the operational convention of the source's proof; it is not derived from a strictly uncontrolled black box.
-- source:
--   Amplitude Estimation from Quantum Signal Processing, arXiv:2207.08628v3, §1.4, Theorem 6, equation (39), PDF p. 14. https://arxiv.org/abs/2207.08628v3 . PDF SHA-256: 877be8e85fc5d29d8d5a914571b5519ec3982d59a2b57fea1ee81704516035e6.

import Definitions.Def_QAlgorithms_Defs_GroverSampling
import Definitions.Def_QAlgorithms_Papers_RoadmapA25_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA25


/-- Sampling from a polynomial: Theorem 6, arXiv:2207.08628v3, PDF p.14, equation (39).
For each polynomial, one instrument works for every completed Grover frame and each
known input label. It samples heads with probability |P(a)|² and retains one of the
four states on every branch. The two conjuncts have their respective oracle APIs.
The absolute constant precedes every polynomial, amplitude, basis and input label.
The bound C(deg(P)+1) includes the constant and zero-polynomial cases, and counts the
oracle calls used to implement the final basis measurement. Controlled ordinary
rotations are allowed as the operational convention used in Proposition 3's proof;
no uncontrolled-black-box implementation of controlled access is asserted. -/
theorem polynomialAmplitudeSampling :
    ∃ C : ℕ, 0 < C ∧
      (∀ P : Polynomial ℂ, IsPellian P →
        ∃ (n : ℕ) (I : GroverSamplingInstrument n),
          (∀ input, ∀ step ∈ I.steps input,
            match step with
            | .opposite _ _ _ => False
            | _ => True) ∧
          (∀ input,
            groverInstrumentQueryCount I input false false +
              groverInstrumentQueryCount I input true false +
              groverInstrumentQueryCount I input false true +
              groverInstrumentQueryCount I input true true ≤ C * (P.natDegree + 1)) ∧
          SamplesWithRetainedSignal I (fun a => P.eval (a : ℂ))) ∧
      (∀ P : Polynomial ℝ, IsSemiPellian P →
        ∃ (n : ℕ) (I : GroverSamplingInstrument n),
          (∀ input, ∀ step ∈ I.steps input,
            match step with
            | .rotation _ _ _ => False
            | _ => True) ∧
          (∀ input,
            groverInstrumentQueryCount I input false false +
              groverInstrumentQueryCount I input true false +
              groverInstrumentQueryCount I input false true +
              groverInstrumentQueryCount I input true true ≤ C * (P.natDegree + 1)) ∧
          SamplesWithRetainedSignal I (fun a => ((P.eval a : ℝ) : ℂ))) := by sorry

end QAlgorithms.Papers.RoadmapA25
