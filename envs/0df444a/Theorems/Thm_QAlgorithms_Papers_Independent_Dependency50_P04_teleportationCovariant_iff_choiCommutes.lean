-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P04_teleportationCovariant_iff_choiCommutes
-- name    : QAlgorithms.Papers.Independent.Dependency50.P04.teleportationCovariant_iff_choiCommutes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:19:06.966431+00:00
-- url     : https://prove2.me/theorems/4a5a8f1c-480b-4a79-a8d3-64e5937937ee
-- title:
--   Finite-dimensional teleportation covariance and the Choi commutator
-- statement:
--   Let $d,e$ be positive integers and let $\mathcal E$ be a completely positive trace-preserving map from a $d$-dimensional input to an $e$-dimensional output. Put $X|j\rangle=|j+1\pmod d\rangle$, $Z|j\rangle=e^{2\pi i j/d}|j\rangle$, and $U_{ab}=X^aZ^b$. Define the normalized Choi state, reference first, by $\rho_{\mathcal E}=d^{-1}\sum_{i,j}|i\rangle\langle j|\otimes\mathcal E(|i\rangle\langle j|)$.
--
--   The channel is teleportation-covariant, meaning that for each $a,b$ a single output unitary $V_{ab}$ satisfies $\mathcal E(U_{ab}\rho U_{ab}^{\dagger})=V_{ab}\mathcal E(\rho)V_{ab}^{\dagger}$ for every density matrix $\rho$, if and only if
--
--   $$
--   \forall a,b\in\{0,\ldots,d-1\},\quad\exists V_{ab}\in\mathrm U(e):\quad [\rho_{\mathcal E},\overline{U_{ab}}\otimes V_{ab}]=0.
--   $$
--
--   The bar denotes entrywise complex conjugation. The output correction need not be a teleportation unitary, and the dimensions may differ. This gives a characterization of teleportation covariance directly from the channel's Choi state.
-- source:
--   Fundamental Limits of Repeaterless Quantum Communications, arXiv:1510.08863v8, PDF p. 14, Eqs.(79)–(80)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P04

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P04

/-- PDF p.14, Eqs.(79)--(80): a finite-dimensional channel is
teleportation-covariant iff each input teleportation matrix U admits an output
unitary V commuting with the normalized Choi matrix through conj(U) tensor V.
The conjugation on U is entrywise; it is not a conjugate transpose. -/
theorem teleportationCovariant_iff_choiCommutes
    {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (Phi : QAlgorithms.Superop (Fin d) (Fin e)) (hPhi : QAlgorithms.IsChannel Phi) :
    IsTeleportationCovariant Phi ↔
      ∀ a b : Fin d, ∃ V : Matrix.unitaryGroup (Fin e) ℂ,
        QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi *
            Matrix.kronecker (fun i j => star (teleportationUnitary d a b i j))
              (V : Matrix (Fin e) (Fin e) ℂ) =
          Matrix.kronecker (fun i j => star (teleportationUnitary d a b i j))
              (V : Matrix (Fin e) (Fin e) ℂ) * QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi Phi := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P04

end
