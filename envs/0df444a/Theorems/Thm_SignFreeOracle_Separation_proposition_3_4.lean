-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_proposition_3_4
-- name    : SignFreeOracle.Separation.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:47.893929+00:00
-- url     : https://prove2.me/theorems/3955c1f8-436d-4a7c-ba45-9229d5ae4321
-- title:
--   Proposition 3.4 — full GPE membership in StoqMA
-- statement:
--   Fix a polynomial degree bound and efficiently known real threshold functions $a,b$ with an inverse-polynomial positive separation. For all labelled simple graphs on $2^m$ vertices with the promised degree bound, the oracle-input spectral promise
--   $$\lambda_{\max}(G)\ge a(m)\quad\text{versus}\quad\lambda_{\max}(G)\le b(m)$$
--   has one polynomial-time uniform StoqMA verifier family. Its verification thresholds are efficient, lie between one half and one, and have an inverse-polynomial gap. Completeness is existential over normalized complex witnesses and soundness universal. No restriction $0\le b<a\le d$ is added. This is membership for the entire GPE problem, including empty spectral regimes, rather than only the hard graph family.
--
--   Differences from the source:
--   - reading: given spectral thresholds a,b → fixed polynomial-time computable threshold functions; reason: known efficient promise parameters are implicit in the computational problem and the StoqMA definition
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Proposition 3.4, p. 10 (PDF p. 10)

import Definitions.Def_SignFreeOracle_Separation_GPE

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

theorem proposition_3_4 (P : GPEParameters) : GPEInStoqMA P := by sorry

end SignFreeOracle.Separation
