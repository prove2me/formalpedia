-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_uniformFilterDimension
-- name    : QAlgorithms.Papers.Independent.Information100.P67.uniformFilterDimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:58:29.433959+00:00
-- url     : https://prove2.me/theorems/86a8a9d0-85e3-41be-86c6-57e11a63ca55
-- title:
--   Proposition 6.2 (Uniform filter dimension)
-- statement:
--   Fix a symmetric factorization of a channel $\mathcal N$ as in Lemma 6.1, with input dimension $a_A$ and common receiver dimension $d_F$. For $n\ge1$ and $0<\delta<1/2$, set $g_n=(n+1)^{a_A^2}$, $c_F=8\log_2(2d_F+1)$, $u=\delta^2/16$, $v=u^2/(32g_n)$, and
--
--   $$b_{\mathcal N}(n,\delta)=c_F\sqrt{n\log_2(2/v^2)}+3\log_2g_n+8\log_2(1/\delta)+19.$$
--
--   For every normalized coherent encoder, form the original pure output on $RF^nE'^{n}E^n$. There is a single filter $Z:F^n\to C$ of positive weight on this state and a CPTP recovery on $CE'^{n}$ which reconstructs $F^nE'^{n}$ to sine-distance error at most $\delta$, preserving the full reference $RE^n$, and satisfying the filter guarantee of Lemma 5.1. Its dimension $L=|C|$ also satisfies
--
--   $$\log_2 L\le nq_{\mathcal N}+b_{\mathcal N}(n,\delta).$$
--
--   Here $R$ includes the sender key and shield in the coding application. The numerical bound is uniform over all correlated inputs; the filter and recovery may depend on the encoder.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 29, Proposition 6.2 (Uniform filter dimension)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Proposition 6.2, PDF pp.29–31. The numerical bound is uniform;
the chosen filter/recovery follow the encoder and may depend on it.
Recovery retains the FULL sender/reference plus E^n, as required by (6.8). -/
theorem uniformFilterDimension [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F]
    (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (hfactor : IsSymmetricFactorization U V)
    (n : ℕ) (hn : 1 ≤ n) (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1 / 2)
    (phi : EuclideanSpace ℂ (R × (Fin n → A))) (hphi : IsState phi) :
    let psi := symmetricEncoderOutput U V n phi
    ∃ L : ℕ, 0 < L ∧ ∃ Z : Matrix (Fin L) (Fin n → F) ℂ,
      ∃ rec : Superop (Fin L × (Fin n → E)) ((Fin n → F) × (Fin n → E)),
        FilterGuarantee psi delta L Z rec ∧
        Real.logb 2 L ≤ (n : ℝ) * maximumCoherentInformation U +
          filterDimensionCorrection (Fintype.card A) (Fintype.card F) n delta := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
