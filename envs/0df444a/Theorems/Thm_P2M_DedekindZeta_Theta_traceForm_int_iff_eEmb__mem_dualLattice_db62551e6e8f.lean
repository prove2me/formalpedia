-- Prove2me | Theorems.Thm_P2M_DedekindZeta_Theta_traceForm_int_iff_eEmb__mem_dualLattice_db62551e6e8f
-- name    : P2M_DedekindZeta_Theta_traceForm_int_iff_eEmb__mem_dualLattice_db62551e6e8f
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:13:19.98987+00:00
-- url     : https://prove2.me/theorems/b80a61b8-1fd3-41ec-9113-1bcbc47602c0
-- title:
--   P2 M Dedekind Zeta Theta trace Form int iff e Emb  mem dual Lattice db62551e6e8f: P2 M Dedekind Zeta Theta trace Form int iff e Emb  mem dual Lattice db62551e6e8f
-- statement:
--   **Trace-dual identification, full `K_ℝ` form** (the standard treatment).
--   An arbitrary
--   point `η : K_ℝ` pairs integrally under the symmetric trace form `T` with every
--   element of `𝔞` iff `eEmbℝ η` lies in the lattice `Λ((𝔞𝔡)⁻¹)` of the dual ideal,
--   equivalently iff `η = mixedEmbedding K b` for some `b ∈ dualIdeal K 𝔞`.
--
--   This is the trace-dual statement that `dual_idealLattice` consumes after writing
--   the Minkowski inner product as `T(cξ, ·)` (`inner_eEmbℝ_eq_traceForm_conjMixed`):
--   taking `η = conjMixed K ξ` gives `eEmbℝ (conjMixed ξ) = conjMink (eEmbℝ ξ)`
--   (`conjMink_apply`), the conjugation-twisted dual lattice membership.
--
--   The reverse direction is `traceForm_mixedEmbedding_int_iff_mem_dualIdeal`. The
--   forward ("fullness") direction — every `η` integral against the full-rank lattice
--   `mixedEmbedding '' 𝔞` is rational, i.e. `η ∈ mixedEmbedding '' K`, hence in
--   `mixedEmbedding '' dualIdeal` — is a standalone lattice-duality / `ℚ`-rationality
--   argument.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L712-L775
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L712-L775

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem P2M_DedekindZeta_Theta_traceForm_int_iff_eEmb__mem_dualLattice_db62551e6e8f
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (η : mixedSpace K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ, traceForm K η a = (k : ℝ)) ↔
      eEmbℝ K η ∈ idealLattice K (dualIdeal K 𝔞) := by sorry

alias «DedekindZeta».«Theta».«traceForm_int_iff_eEmbℝ_mem_dualLattice» := P2M_DedekindZeta_Theta_traceForm_int_iff_eEmb__mem_dualLattice_db62551e6e8f
