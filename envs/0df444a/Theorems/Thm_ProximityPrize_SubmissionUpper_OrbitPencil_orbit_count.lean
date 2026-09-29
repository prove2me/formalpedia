-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_OrbitPencil_orbit_count
-- name    : ProximityPrize.SubmissionUpper.OrbitPencil.orbit_count
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T05:27:52.883906+00:00
-- url     : https://prove2.me/theorems/17e1c4dc-8483-46ea-ba80-fc934ca802d1
-- title:
--   ProximityPrize.SubmissionUpper.OrbitPencil.orbit_count
-- statement:
--   /-
--   Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
--   Released under Apache 2.0 license as described in the file LICENSE.
--   -/
--
--   Checked source proof from the Proximity Prize upper record, introduced in the submission credited to erdkocak. Verified from Lean 4.32.2 to 4.33.1 with the reviewed manual import-context repair; this is not a claim of competition acceptance.
--
--   Original source license:
--
--                                    Apache License
--                              Version 2.0, January 2004
--                           http://www.apache.org/licenses/
--
--      TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION
--
--      1. Definitions.
--
--         "License" shall mean the terms and conditions for use, reproduction,
--         and distribution as defined by Sections 1 through 9 of this document.
--
--         "Licensor" shall mean the copyright owner or entity authorized by
--         the copyright owner that is granting the License.
--
--         "Legal Entity" shall mean the union of the acting entity and all
--         other entities that control, are controlled by, or are under common
--         control with that entity. For the purposes of this definition,
--         "control" means (i) the power, direct or indirect, to cause the
--         direction or management of such entity, whether by contract or
--         otherwise, or (ii) ownership of fifty percent (50%) or more of the
--         outstanding shares, or (iii) beneficial ownership of such entity.
--
--         "You" (or "Your") shall mean an individual or Legal Entity
--         exercising permissions granted by this License.
--
--         "Source" form shall mean the preferred form for making modifications,
--         including but not limited to software source code, documentation
--         source, and configuration files.
--
--         "Object" form shall mean any form resulting from mechanical
--         transformation or translation of a Source form, including but
--         not limited to compiled object code, generated documentation,
--         and conversions to other media types.
--
--         "Work" shall mean the work of authorship, whether in Source or
--         Object form, made available under the License, as indicated by a
--         copyright notice that is included in or attached to the work
--         (an example is provided in the Appendix below).
--
--         "Derivative Works" shall mean any work, whether in Source or Object
--         form, that is based on (or derived from) the Work and for which the
--         editorial revisions, annotations, elaborations, or other modifications
--         represent, as a whole, an original work of authorship. For the purposes
--         of this License, Derivative Works shall not include works that remain
--         separable from, or merely link (or bind by name) to the interfaces of,
--         the Work and Derivative Works thereof.
--
--         "Contribution" shall mean any work of authorship, including
--         the original version of the Work and any modifications or additions
--         to that Work or Derivative Works thereof, that is intentionally
--         submitted to Licensor for inclusion in the Work by the copyright owner
--         or by an individual or Legal Entity authorized to submit on behalf of
--         the copyright owner. For the purposes of this definition, "submitted"
--         means any form of electronic, verbal, or written communication sent
--         to the Licensor or its representatives, including but not limited to
--         communication on electronic mailing lists, source code control systems,
--         and issue tracking systems that are managed by, or on behalf of, the
--         Licensor for the purpose of discussing and improving the Work, but
--         excluding communication that is conspicuously marked or otherwise
--         designated in writing by the copyright owner as "Not a Contribution."
--
--         "Contributor" shall mean Licensor and any individual or Legal Entity
--         on behalf of whom a Contribution has been received by Licensor and
--         subsequently incorporated within the Work.
--
--      2. Grant of Copyright License. Subject to the terms and conditions of
--         this License, each Contributor hereby grants to You a perpetual,
--         worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--         copyright license to reproduce, prepare Derivative Works of,
--         publicly display, publicly perform, sublicense, and distribute the
--         Work and such Derivative Works in Source or Object form.
--
--      3. Grant of Patent License. Subject to the terms and conditions of
--         this License, each Contributor hereby grants to You a perpetual,
--         worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--         (except as stated in this section) patent license to make, have made,
--         use, offer to sell, sell, import, and otherwise transfer the Work,
--         where such license applies only to those patent claims licensable
--         by such Contributor that are necessarily infringed by their
--         Contribution(s) alone or by combination of their Contribution(s)
--         with the Work to which such Contribution(s) was submitted. If You
--         institute patent litigation against any entity (including a
--         cross-claim or counterclaim in a lawsuit) alleging that the Work
--         or a Contribution incorporated within the Work constitutes direct
--         or contributory patent infringement, then any patent licenses
--         granted to You under this License for that Work shall terminate
--         as of the date such litigation is filed.
--
--      4. Redistribution. You may reproduce and distribute copies of the
--         Work or Derivative Works thereof in any medium, with or without
--         modifications, and in Source or Object form, provided that You
--         meet the following conditions:
--
--         (a) You must give any other recipients of the Work or
--             Derivative Works a copy of this License; and
--
--         (b) You must cause any modified files to carry prominent notices
--             stating that You changed the files; and
--
--         (c) You must retain, in the Source form of any Derivative Works
--             that You distribute, all copyright, patent, trademark, and
--             attribution notices from the Source form of the Work,
--             excluding those notices that do not pertain to any part of
--             the Derivative Works; and
--
--         (d) If the Work includes a "NOTICE" text file as part of its
--             distribution, then any Derivative Works that You distribute must
--             include a readable copy of the attribution notices contained
--             within such NOTICE file, excluding those notices that do not
--             pertain to any part of the Derivative Works, in at least one
--             of the following places: within a NOTICE text file distributed
--             as part of the Derivative Works; within the Source form or
--             documentation, if provided along with the Derivative Works; or,
--             within a display generated by the Derivative Works, if and
--             wherever such third-party notices normally appear. The contents
--             of the NOTICE file are for informational purposes only and
--             do not modify the License. You may add Your own attribution
--             notices within Derivative Works that You distribute, alongside
--             or as an addendum to the NOTICE text from the Work, provided
--             that such additional attribution notices cannot be construed
--             as modifying the License.
--
--         You may add Your own copyright statement to Your modifications and
--         may provide additional or different license terms and conditions
--         for use, reproduction, or distribution of Your modifications, or
--         for any such Derivative Works as a whole, provided Your use,
--         reproduction, and distribution of the Work otherwise complies with
--         the conditions stated in this License.
--
--      5. Submission of Contributions. Unless You explicitly state otherwise,
--         any Contribution intentionally submitted for inclusion in the Work
--         by You to the Licensor shall be under the terms and conditions of
--         this License, without any additional terms or conditions.
--         Notwithstanding the above, nothing herein shall supersede or modify
--         the terms of any separate license agreement you may have executed
--         with Licensor regarding such Contributions.
--
--      6. Trademarks. This License does not grant permission to use the trade
--         names, trademarks, service marks, or product names of the Licensor,
--         except as required for reasonable and customary use in describing the
--         origin of the Work and reproducing the content of the NOTICE file.
--
--      7. Disclaimer of Warranty. Unless required by applicable law or
--         agreed to in writing, Licensor provides the Work (and each
--         Contributor provides its Contributions) on an "AS IS" BASIS,
--         WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
--         implied, including, without limitation, any warranties or conditions
--         of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
--         PARTICULAR PURPOSE. You are solely responsible for determining the
--         appropriateness of using or redistributing the Work and assume any
--         risks associated with Your exercise of permissions under this License.
--
--      8. Limitation of Liability. In no event and under no legal theory,
--         whether in tort (including negligence), contract, or otherwise,
--         unless required by applicable law (such as deliberate and grossly
--         negligent acts) or agreed to in writing, shall any Contributor be
--         liable to You for damages, including any direct, indirect, special,
--         incidental, or consequential damages of any character arising as a
--         result of this License or out of the use or inability to use the
--         Work (including but not limited to damages for loss of goodwill,
--         work stoppage, computer failure or malfunction, or any and all
--         other commercial damages or losses), even if such Contributor
--         has been advised of the possibility of such damages.
--
--      9. Accepting Warranty or Additional Liability. While redistributing
--         the Work or Derivative Works thereof, You may choose to offer,
--         and charge a fee for, acceptance of support, warranty, indemnity,
--         or other liability obligations and/or rights consistent with this
--         License. However, in accepting such obligations, You may act only
--         on Your own behalf and on Your sole responsibility, not on behalf
--         of any other Contributor, and only if You agree to indemnify,
--         defend, and hold each Contributor harmless for any liability
--         incurred by, or claims asserted against, such Contributor by reason
--         of your accepting any such warranty or additional liability.
--
--      END OF TERMS AND CONDITIONS
--
--      APPENDIX: How to apply the Apache License to your work.
--
--         To apply the Apache License to your work, attach the following
--         boilerplate notice, with the fields enclosed by brackets "{}"
--         replaced with your own identifying information. (Don't include
--         the brackets!)  The text should be enclosed in the appropriate
--         comment syntax for the file format. We also recommend that a
--         file or class name and description of purpose be included on the
--         same "printed page" as the copyright notice for easier
--         identification within third-party archives.
--
--      Copyright {yyyy} {name of copyright owner}
--
--      Licensed under the Apache License, Version 2.0 (the "License");
--      you may not use this file except in compliance with the License.
--      You may obtain a copy of the License at
--
--          http://www.apache.org/licenses/LICENSE-2.0
--
--      Unless required by applicable law or agreed to in writing, software
--      distributed under the License is distributed on an "AS IS" BASIS,
--      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
--      See the License for the specific language governing permissions and
--      limitations under the License.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/224323f053d0d1dfa78d7b9625194fe0133f04bc/ProximityPrize/SubmissionUpper/OrbitPencil.lean
--
--   yukon-proof-operation:bootstrap-14d70594487b4432c5e7765736615ff34029d65df7207c0c81a9947b0d5f100a
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLTE0ZDcwNTk0NDg3YjQ0MzJjNWU3NzY1NzM2NjE1ZmYzNDAyOWQ2NWRmNzIwN2MwYzgxYTk5NDdiMGQ1ZjEwMGEiLCJoYXNoIjoiNzg4NDY0NjUyZTVkNWIyZmM4NDQ2NmNiMDNlMTI3ODNlYjAzY2ZhYjU2MjNjMTgyMDBmOTg1NDM0ZmQ3NzQ5NSIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLk9yYml0UGVuY2lsLm9yYml0X2NvdW50IiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoicHJveGltaXR5LXByaXplIn0]

import Mathlib
import Init
/-!
# A rational pencil on the 512-by-512 NTT grid

The size-`2^18` NTT domain is partitioned into 512 fibres by `x ↦ x^512`.
We use 272 whole fibres together with a fixed 511-point core.  Prescribing 14
top coefficients and the product of the selected fibre labels leaves more than
`2^59` choices while forcing pairwise differences to have the two roots needed
to fit under the row-degree budget.
-/

namespace ProximityPrize.SubmissionUpper.OrbitPencil

open Polynomial
                                   
                             
open scoped NNReal BigOperators

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem orbit_count :
    ((2 ^ 31 - 2 ^ 24 + 1)^14 * 512) * 2^59 < Nat.choose 511 272 := by sorry
end OrbitPencil
end SubmissionUpper
end ProximityPrize
