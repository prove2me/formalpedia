-- Prove2me | Theorems.Thm_QuantumHMMR_lemma_4_2
-- name    : QuantumHMMR.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:30.684443+00:00
-- url     : https://prove2.me/theorems/c824b29b-3772-4ed1-a9d6-a475e327f2fe
-- title:
--   Lemma 4.2 — spectral gaps of the Clifford walk (projectors, rank $D_t$, gaps (13), (14))
-- statement:
--   Let $G$ be an admissible generating set and fix $t \ge 4$.
--
--   1. The moment operators $M^{(t)}_{\mathcal C_n}$ and $M^{(t)}_{\mu_H}$ are orthogonal projectors onto the Clifford- and Haar-invariant subspaces, respectively, the latter contained in the former.
--   2. For all sufficiently large $n$,
--   $$
--   \operatorname{rank} M^{(t)}_{\mathcal C_n} = D_t = \prod_{j=0}^{t-2}(2^j + 1). \tag{12}
--   $$
--   3. There are universal constants $\gamma, a > 0$ such that, for all sufficiently large $n$, the local Clifford moment operator has absolute spectral gap at least $\gamma/n$ outside the Clifford-invariant subspace,
--   $$
--   \big\|M^{(t)}_{\chi_n} - M^{(t)}_{\mathcal C_n}\big\|_\infty \le 1 - \frac{\gamma}{n}, \tag{13}
--   $$
--   and on the Clifford-invariant subspace the insertion averaged between Clifford twirls has gap at least $a$ outside the Haar-invariant subspace,
--   $$
--   M^{(t)}_{\mathcal C_n}\big(I - M^{(t)}_{\xi_n}\big) M^{(t)}_{\mathcal C_n} \succeq a\big(M^{(t)}_{\mathcal C_n} - M^{(t)}_{\mu_H}\big). \tag{14}
--   $$
--
--   The paper cites these facts from Gross–Nezami–Walter [GNW21] and [BH26]; they are the spectral input of the proof of Theorem 1.3.
--
--   Differences from the source:
--   - reading: "Fix t ≥ 4 … There are universal constants γ, a > 0" → γ, a chosen after G and before t (independent of t and n); n₀ depends on t; reason: the stronger of the two readings of "universal" (rule 6); the goal needs only per-t constants
--   - encoding: orthogonal projector onto the invariant subspace → Hermitian, idempotent, and its fixed vectors are exactly the vectors fixed by every U^{⊗t} ⊗ Ū^{⊗t} (U Clifford, resp. unitary); reason: same objects
--   - encoding: C_n with the uniform distribution → published cliffordLaw n, with the finiteness of the Clifford group modulo phase as an instance argument; reason: the group is finite and the uniform law does not depend on the enumeration
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.2, Eqs. (12)–(14), p.13

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_IsCliffordGenSet
import Definitions.Def_QuantumHMMR_momentRep
import Definitions.Def_QuantumHMMR_Dt
import Definitions.Def_QuantumHMMR_IsGapPair

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45
open scoped Matrix

namespace QuantumHMMR

/-- **Lemma 4.2** (spectral gaps of the Clifford walk; Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.13, summarizing [GNW21], [BH26]).
Fix `t ≥ 4`.
1. The moment operators `M^{(t)}_{C_n}` and `M^{(t)}_{μ_H}` are orthogonal projectors onto the
   Clifford- and Haar-invariant subspaces, respectively, the latter contained in the former.
2. For all sufficiently large `n`, `rank M^{(t)}_{C_n} = D_t = ∏_{j=0}^{t-2} (2^j + 1)` (12).
3. There are universal constants `γ, a > 0` such that, for all large `n`,
   `‖M^{(t)}_{χ_n} - M^{(t)}_{C_n}‖_∞ ≤ 1 - γ/n` (13) and
   `M^{(t)}_{C_n} (I - M^{(t)}_{ξ_n}) M^{(t)}_{C_n} ⪰ a (M^{(t)}_{C_n} - M^{(t)}_{μ_H})` (14).

**Formalization Note** "Orthogonal projector onto the invariant subspace": Hermitian, idempotent,
and its fixed vectors are exactly the vectors `v` with `(U^{⊗t} ⊗ Ū^{⊗t}) v = v` for every Clifford
`U` (resp. every unitary `U`). The constants `γ, a` are chosen after the generating set `G` and
before `t` ("universal"); `n₀` depends on `t`. Clause 3 is `IsGapPair G t γ a` for every `t ≥ 4`.
The finiteness of the Clifford group modulo phase is an instance argument. -/
theorem lemma_4_2 [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G) :
    (∀ t ≥ 4, ∀ n : ℕ,
      (balancedUnitaryMoment (cliffordLaw n) t).IsHermitian ∧
      balancedUnitaryMoment (cliffordLaw n) t * balancedUnitaryMoment (cliffordLaw n) t =
        balancedUnitaryMoment (cliffordLaw n) t ∧
      (∀ v, balancedUnitaryMoment (cliffordLaw n) t *ᵥ v = v ↔
        ∀ C : Clifford.normalizer n, momentRep t C.val.val *ᵥ v = v) ∧
      (balancedUnitaryMoment (haarLaw n) t).IsHermitian ∧
      balancedUnitaryMoment (haarLaw n) t * balancedUnitaryMoment (haarLaw n) t =
        balancedUnitaryMoment (haarLaw n) t ∧
      (∀ v, balancedUnitaryMoment (haarLaw n) t *ᵥ v = v ↔
        ∀ U ∈ Matrix.unitaryGroup (Qubits n) ℂ, momentRep t U *ᵥ v = v) ∧
      (∀ v, balancedUnitaryMoment (haarLaw n) t *ᵥ v = v →
        balancedUnitaryMoment (cliffordLaw n) t *ᵥ v = v)) ∧
    (∀ t ≥ 4, ∃ n₀ : ℕ, ∀ n ≥ n₀, (balancedUnitaryMoment (cliffordLaw n) t).rank = Dt t) ∧
    ∃ γ a : ℝ, ∀ t ≥ 4, IsGapPair G t γ a := by sorry

end QuantumHMMR
