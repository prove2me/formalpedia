-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_freeMapsSpectatorsEmbeddings
-- name    : QAlgorithms.Papers.Independent.Information100.P21.freeMapsSpectatorsEmbeddings
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:00:16.993086+00:00
-- url     : https://prove2.me/theorems/60cce665-efa1-45e5-a32b-10df41c60a42
-- title:
--   X.22 — Lemma X.22 (Free maps, spectators, and local embeddings). If a completely positive trace-preserving map Φ sends
-- statement:
--   Let $\Phi$ be a CPTP map between positive finite multipartite registers that sends fully separable states to fully separable states. For each $\nu\in\{s,g\}$,
--   $$R_\nu^{\mathrm{FS}_M}(\Phi(\rho))\le R_\nu^{\mathrm{FS}_N}(\rho).$$
--   Equality holds when a CPTP left inverse also preserves the corresponding free sets. Adjoining any fully separable spectator, possibly mixed and classically correlated among its own parties, preserves both values. Rectangular local isometries also preserve both values. These are free maps for the displayed full-separability partitions.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 28, X.22 — Lemma X.22 (Free maps, spectators, and local embeddings). If a completely positive trace-preserving map Φ sends

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 28, Lemma X.22 (Free maps, spectators, and local embeddings). If a completely positive trace-preserving map Φ sends. -/
theorem freeMapsSpectatorsEmbeddings {P Q : Type*} [Fintype P] [Fintype Q]
  (d : P → ℕ) (e : Q → ℕ) (hd : ∀ j,0<d j) (he : ∀ j,0<e j)
  (Phi : QAlgorithms.Superop (Config d) (Config e)) (hc : QAlgorithms.IsChannel Phi)
  (hf : ∀ sigma, sigma∈fs d → Phi sigma∈fs e)
  (rho : Op (Config d)) (hr : QAlgorithms.IsDensityMatrix rho) :
  (∀ standard : Bool, fsR e standard (Phi rho)≤fsR d standard rho) ∧
  ((∃ Psi : QAlgorithms.Superop (Config e) (Config d), QAlgorithms.IsChannel Psi ∧
      (∀ sigma, sigma∈fs e → Psi sigma∈fs d) ∧ (∀ X, Psi (Phi X)=X)) →
    ∀ standard : Bool, fsR e standard (Phi rho)=fsR d standard rho) ∧
  (∀ eta : Op (Config e), eta∈fs e → ∀ standard : Bool,
    fsR (Sum.elim d e) standard (spectator rho eta)=fsR d standard rho) ∧
  (∀ (f : P → ℕ) (V : (j : P) → Matrix (Fin (f j)) (Fin (d j)) ℂ),
    (∀ j,0<f j) → (∀ j,(V j)ᴴ*V j=1) → ∀ standard : Bool,
    fsR f standard (localTensor V*rho*(localTensor V)ᴴ)=fsR d standard rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
