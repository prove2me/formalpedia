-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA03_amplitudeAmplification_polynomial
-- name    : QAlgorithms.Papers.RoadmapA03.amplitudeAmplification_polynomial
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:33:52.140131+00:00
-- url     : https://prove2.me/theorems/7fb1560b-7ed9-44ac-ae67-c288f1293350
-- title:
--   Amplitude amplification: exact rank-one polynomial transformation
-- statement:
--   Fix a nonnegative integer $l$, put $d=2l+1$, and choose real phases $\phi_0,\ldots,\phi_{d-1}$. There are complex polynomials $P,Q$, depending only on these phases and $l$, with $\deg P\le d$, $\deg Q\le d-1$, and respective parities $d$ and $d-1$ modulo $2$, such that
--
--   $$
--   |P(x)|^2+(1-x^2)|Q(x)|^2=1 \qquad\text{for every }x\in[-1,1].
--   $$
--
--   For every finite quantum register, every pair of normalized pure states $|A_0\rangle,|B_0\rangle$ in that register, and every unitary $U$ with a real nonzero amplitude $a=\langle A_0|U|B_0\rangle$, define the available exact rank-one phase shifts $A_\phi=e^{i\phi|A_0\rangle\langle A_0|}$ and $B_\phi=e^{i\phi|B_0\rangle\langle B_0|}$ for real $\phi$. Then
--
--   $$
--   \langle A_0|A_{\phi_0}\left[\prod_{k=1}^{l}U B_{\phi_{2k-1}}U^\dagger A_{\phi_{2k}}\right]U|B_0\rangle=P(a).
--   $$
--
--   The product is written in increasing $k$ from left to right, and its rightmost $U$ acts first. Normalization and unitarity imply $a\in[-1,1]$; the endpoints $a=\pm1$ are allowed. Parity means $P(-x)=(-1)^dP(x)$ and $Q(-x)=(-1)^{d-1}Q(x)$.
--
--   This construction applies one uniform polynomial to a privileged transition amplitude and connects amplitude amplification with quantum signal processing.
--
--   **Formalization Note** The finite register is a Euclidean space over an arbitrary finite basis type. The frozen positive-sign rank-one phase shifts and sequence encode Eq. (13) exactly. The complementary polynomial is existentially quantified with $P$ before the register, states, unitary and amplitude. The zero polynomial is allowed as $Q$, including when $l=0$.
-- source:
--   A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, Theorem 2 (Amplitude Amplification), Section II B, Eq. (13), PDF p. 5. https://arxiv.org/abs/2105.02859v5 . PDF SHA-256: a3e93f87dad644dee3b97d5f780f60c3e5a19a2d1cf22896484258d4ab582730.

import Definitions.Def_QAlgorithms_Defs_RankOneAmplitudeSequence
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapA03

universe u

/-- Martyn, Rossi, Tan and Chuang, *A Grand Unification of Quantum Algorithms*,
arXiv:2105.02859v5, Theorem 2 (Amplitude Amplification), PDF/printed p.5, Eq. (13),
with the standing conventions of Section II B (p.4) and the polynomial conditions
of Theorem 1 (pp.3–4). For an odd length `d = 2 * l + 1` and real phases,
the same complex polynomial transforms every real nonzero rank-one amplitude.
The complementary polynomial carries the full degree, parity and normalization
conditions. The exact positive-sign rank-one shifts and increasing, left-to-right
product order are those of `RankOneAA.sequence`; no ambient Hermiticity is assumed.
-/
theorem amplitudeAmplification_polynomial (l : ℕ) (phi : Fin (2 * l + 1) → ℝ) :
    ∃ P Q : Polynomial ℂ,
      P.natDegree ≤ 2 * l + 1 ∧
      Q.natDegree ≤ 2 * l ∧
      HasParity P (2 * l + 1) ∧
      HasParity Q (2 * l) ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1) ∧
      ∀ (I : Type u) [Fintype I] [DecidableEq I]
        (A0 B0 : EuclideanSpace ℂ I) (hA : IsState A0) (hB : IsState B0)
        (U : Matrix.unitaryGroup I ℂ) (a : ℝ),
        a ≠ 0 → inner ℂ A0 (act (U : Matrix I I ℂ) B0) = (a : ℂ) →
        inner ℂ A0 (act (RankOneAA.sequence A0 B0 hA hB U l phi) B0) =
          P.eval (a : ℂ) := by sorry

end QAlgorithms.Papers.RoadmapA03
