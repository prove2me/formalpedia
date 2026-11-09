-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_valid_certificate
-- name    : QMAPerfectCompleteness.Main.valid_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:33.20837+00:00
-- url     : https://prove2.me/theorems/e7a514c6-428f-40d9-b8c4-de2d4291cafe
-- title:
--   Lemma 3.7 — a valid certificate with $a/b=\Gamma_z>2$
-- statement:
--   On a YES instance there is a valid certificate $(z,a,b)$ with
--
--   $$
--   \frac ab=\Gamma_z>2.
--   $$
--
--   Here $k$ and $M=2^k$ are fixed from $h$ and $\ell$ before the certificate is chosen, and validity means $a,b$ are positive integers representable by $k$ bits with $M/8\le a\le M/4$ and $2b\le a$. The equality $a/b=\Gamma_z$ is exact, in the reals. This supplies the classical part of the honest prover's proof. The prover need not compute it efficiently.
--
--   Differences from the source:
--   - generalization: the fixed verifier $V$ of Lemma 3.1 on one input, with $g\ge1$ → any verifier $V$ over $\mathcal G_2$, with no lower bound on $g$, a YES instance being a verifier that accepts some proof with probability at least $2/3$; reason: the statement specializes to the source's verifier on any YES input, and the bounds used hold for $g=0$ as well
--   - encoding: the scalar $\Gamma_z=\langle z|A^\ell|z\rangle$ → the real part of that matrix entry; reason: $A^\ell$ is Hermitian, so its diagonal entry is real
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 11, Lemma 3.7

import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding

namespace QMAPerfectCompleteness.Main

/-- Lemma 3.7 (p. 11): on a YES instance there is a valid certificate with `a/b = Γ_z > 2`. -/
theorem valid_certificate (V : Verifier gatesG2) (hyes : V.AcceptsSomeProof (2 / 3)) :
    ∃ (z : V.Proof) (a b : ℕ), IsValidCertificate V a b ∧
      (a : ℝ) / b = V.gamma z ∧ 2 < V.gamma z := by sorry

end QMAPerfectCompleteness.Main
