-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_binomial_spinEmbeddings
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.binomial_spinEmbeddings
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:32:16.131673+00:00
-- url     : https://prove2.me/theorems/a2130631-0dc6-4d94-9575-76475eeace48
-- title:
--   Antipodal spin coefficients and isometric embeddings
-- statement:
--   Let $N,S\ge0$ be integers, $M=N+1$, $J=M/2>0$, and let an integer $K\ge(S+1)M$ count physical qubits. On spin labels $m=0,\ldots,M$, set $v_\mu(m)=2^{-M/2}(-1)^{\mu m}\sqrt{\binom M m}$. The usual spin-x matrix satisfies
--
--   $$J_xv_\mu=(-1)^\mu\frac M2v_\mu.$$
--
--   The following three basis maps preserve inner products of all coefficient vectors: $|m\rangle\mapsto|(S+1)m\rangle$ in one oscillator; $|m\rangle\mapsto|(S+1)(M-m),(S+1)m\rangle$ in two oscillators; and $|m\rangle\mapsto|D^K_{(S+1)m}\rangle$, where the Dicke vector is the normalized equal sum of $K$-qubit words of the indicated weight. The first image of $v_\mu$ is precisely the single-mode binomial codeword. The other images supply the two-mode and permutation-invariant descriptions. The two-mode total photon number is $(S+1)M$, so its physical Schwinger spin is $(S+1)M/2$, distinct from the coefficient spin $M/2$.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 14, §VI C, (6.11)–(6.16), Fig.7(a): spin-coherent characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.14--15 (6.11)--(6.16): antipodal eigenvectors and their three isometric
coefficient embeddings. The physical Schwinger spin is (S+1)M/2; the transported
coefficient spin is M/2. Neither is silently substituted for the other.
Printed (6.16): 2J-(S+1)m; changed to (S+1)(2J-m), following the
preceding basis map and Fig.7(a), to retain fixed total occupation. -/
theorem binomial_spinEmbeddings (N S K : ℕ) (hK : (S + 1) * (N + 1) ≤ K) :
    (∀ mu : Fin 2, (spinX (N + 1)).mulVec (antipodal (N + 1) mu) =
      ((-1 : ℂ) ^ mu.val * ((N + 1 : ℕ) : ℂ) / 2) • antipodal (N + 1) mu ∧
      embedOne (N + 1) S (antipodal (N + 1) mu) = binomialCodeCoordinates N S mu) ∧
    (∀ v w : Fin (N + 2) → ℂ,
      fockInner (embedOne (N + 1) S v) (embedOne (N + 1) S w) = ∑ m, conj (v m) * w m) ∧
    (∀ v w : Fin (N + 2) → ℂ,
      (∑' n : ℕ × ℕ, conj (embedTwo (N + 1) S v n) * embedTwo (N + 1) S w n) =
        ∑ m, conj (v m) * w m) ∧
    (∀ v w : Fin (N + 2) → ℂ,
      (∑ x : Fin K → Fin 2, conj (embedDicke (N + 1) S K v x) * embedDicke (N + 1) S K w x) =
        ∑ m, conj (v m) * w m) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
