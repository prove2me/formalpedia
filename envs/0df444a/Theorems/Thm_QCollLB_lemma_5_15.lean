-- Prove2me | Theorems.Thm_QCollLB_lemma_5_15
-- name    : QCollLB.lemma_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:15:18.239204+00:00
-- url     : https://prove2.me/theorems/4a0617bf-85af-47f8-ad53-5d950edc0348
-- title:
--   Lemma 5.15 — properties of the encoding $V$
-- statement:
--   Let $n\ge1$. The completion maps and the encoding satisfy
--   $$
--   V^\dagger V=I_P,\qquad AV=\Gamma_n^{1/2},\qquad VV^\dagger=K_RK_D,\qquad A_sK^{(s)}_R=A_sK^{(s)}_D=P_{P_s}A_s\quad(0\le s\le n).
--   $$
--
--   So $V$ is an isometry from the permutation register onto the database vectors that are both range- and domain-harmonic, and completion intertwines the harmonic projections with the degree projections.
--
--   Differences from the source:
--   - encoding: A_s : D_s → P and K^{(s)} : D_s → D_s → both extended by 0 to all of D; the identities are compared on D; reason: both sides vanish off D_s, so this is the identity on D_s
--   - reading: n arbitrary (implicitly n ≥ 1) → hypothesis 1 ≤ n; reason: for n = 0 the decomposition P = ⊕_{s=0}^{n−1} P_s of p.24 is an empty sum while P ≠ 0; the paper only uses n ≥ 2k
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 5.15, Eq. (46), p.32

import Mathlib
import Definitions.Def_QCollLB_Harmonic

namespace QCollLB

open CompPermOracle

/-- **Lemma 5.15 (Properties of the encoding)** (Peng–Wu, arXiv:2611.01767 (PDF sha256
4e5aba34…d9fc), Lemma 5.15, Eq. (46), p.32). The completion maps and the encoding satisfy
`V†V = I_P`, `AV = Γ_n^{1/2}`, `VV† = K_R K_D`, and `A_s K^{(s)}_R = A_s K^{(s)}_D = P_{P_s} A_s` for
every database size `s`.

**Formalization Note.** `A_s` (on `D_s`) is extended by `0` to `D` as `CompPermOracle.synth n s`, and
`K^{(s)}_R`, `K^{(s)}_D` are the projectors of `D` onto `D^{(s)}_R`, `D^{(s)}_D ⊆ D_s`; both sides of the
last identities vanish off `D_s`, so they are the paper's identities on `D_s`. `s` ranges over
`0 ≤ s ≤ n` (Definition 5.12). `n ≥ 1`: for `n = 0` the paper's decomposition
`P = ⨁_{s=0}^{n−1} P_s` (p.24) is an empty sum while `P = ℂ[S_0] ≠ 0`. -/
theorem lemma_5_15 (n : ℕ) (hn : 1 ≤ n) :
    (ContinuousLinearMap.adjoint (V n)).comp (V n) = 1 ∧
      (Asyn n).comp (V n) = GammaSqrt n ∧
      (V n).comp (ContinuousLinearMap.adjoint (V n)) = (KR n).comp (KD n) ∧
      ∀ s ≤ n, (synth n s).comp (KRs n s) = (PsSub n s).starProjection.comp (synth n s) ∧
        (synth n s).comp (KDs n s) = (PsSub n s).starProjection.comp (synth n s) := by sorry

end QCollLB
